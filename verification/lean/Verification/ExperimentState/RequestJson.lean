import Lean.Data.Json
import Verification.ExperimentState.CertificateProducer

/-! Versioned, in-memory JSON boundary for the stateful consumer. A request and
its evidence are separate inputs. This is a calculus protocol, not a decoder
for SKJS types or a TypeScript extractor. No unsupported type is approximated. -/
namespace Verification.ExperimentState.RequestJson
open Lean ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open ProgramCertificates PointClaims ControlFlow CertificateProducer

deriving instance ToJson, FromJson for Tag
deriving instance ToJson, FromJson for Tm
deriving instance ToJson, FromJson for Clause
deriving instance ToJson, FromJson for Target
deriving instance ToJson, FromJson for Continuation
deriving instance ToJson, FromJson for Node
deriving instance ToJson, FromJson for PositiveCertificates.ArrowCert
deriving instance ToJson, FromJson for PositiveCertificates.Certificate
deriving instance ToJson, FromJson for PositiveCertificates.Proof
deriving instance ToJson, FromJson for Sequent
deriving instance ToJson, FromJson for Rule
deriving instance ToJson, FromJson for ProgramCertificates.Evidence
deriving instance ToJson, FromJson for NodeEvidence
deriving instance ToJson, FromJson for PointClaim

structure Request where
  version : Nat
  types : List (List (Clause (List Nat)))
  program : Program
  claims : List (PointClaim Nat)
  result : Ty Nat
  start : Nat
  /-- External argument contract, in slot order; independent of point claims. -/
  inputs : List (Ty Nat)
  deriving ToJson, FromJson

structure Response where
  version : Nat
  certificate : ControlFlow.Certificate Nat
  deriving ToJson, FromJson

def graph (r : Request) : NormalGraph Nat := fun i => r.types[i]?.getD []

def validTy (bound : Nat) (A : Ty Nat) : Bool := A.all (fun i => i < bound)

def clauseTypes : Clause (Ty Nat) → List (Ty Nat)
  | .nul | .bool | .boolLit _ => []
  | .refs A bs => A :: bs
  | .arrs L => L.flatMap (fun p => [p.1,p.2])

def validClaim (bound : Nat) (c : PointClaim Nat) : Bool :=
  (c.type :: c.context).all (validTy bound)

/-- The total Lean graph's out-of-range default must not become an accidental
meaning for an invalid serialized type reference. -/
def validRequest (r : Request) : Bool :=
  r.version == 2 && (r.types.flatMap id |>.flatMap clauseTypes).all (validTy r.types.length) &&
  r.claims.all (validClaim r.types.length) && validTy r.types.length r.result &&
  r.inputs.all (validTy r.types.length)

def arrowTypes : PositiveCertificates.ArrowCert Nat → List (Ty Nat)
  | .empty => []
  | .source p => [p.1,p.2]
  | .union a b l r | .combine a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)

def proofTypes : PositiveCertificates.Proof Nat → List (Ty Nat)
  | .subset => []
  | .trans middle l r => middle :: (proofTypes l ++ proofTypes r)
  | .core c => c.table.flatMap (fun p => [p.1,p.2]) ++ c.arrows.flatMap (fun e =>
      e.1.flatMap (fun p => [p.1,p.2]) ++ [e.2.1.1,e.2.1.2] ++ arrowTypes e.2.2)

def validEvidence (bound : Nat) : ProgramCertificates.Evidence Nat → Bool
  | .node j r ps =>
    (j.type :: j.context).all (validTy bound) &&
    (match r with
      | .sub p => (proofTypes p).all (validTy bound)
      | .ifBoolVar T F => validTy bound T && validTy bound F
      | _ => true) &&
    ps.attach.all (fun p => validEvidence bound p.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

def validResponse (r : Request) (c : Response) : Bool :=
  c.version == 2 && c.certificate.all (fun n =>
    validEvidence r.types.length n.expression &&
    (n.edges.flatMap id |>.flatMap proofTypes).all (validTy r.types.length))

/-- Semantic JSON equality for strict field checking, independent of object
field order. Re-encoding rejects unknown fields and defaulted omissions. -/
partial def sameJson (a b : Json) : Bool :=
  match a, b with
  | .arr xs, .arr ys => xs.size == ys.size && (xs.toList.zip ys.toList).all (fun (x,y) => sameJson x y)
  | .obj xs, .obj ys => xs.toList.length == ys.toList.length && xs.toList.all (fun (k,v) =>
      match b.getObjVal? k with | .ok w => sameJson v w | .error _ => false)
  | _, _ => a == b

def decodeStrict [FromJson α] [ToJson α] (j : Json) : Except String α := do
  let a ← fromJson? j
  if sameJson j (toJson a) then return a
  throw "unknown fields or missing explicit fields in the versioned calculus protocol"

def decodeRequest (j : Json) : Except String Request := do
  let r ← decodeStrict j
  if validRequest r then return r
  throw "unsupported request version or out-of-range type label"

def decodeResponse (r : Request) (j : Json) : Except String Response := do
  let c ← decodeStrict j
  if validResponse r c then return c
  throw "unsupported evidence version or out-of-range type label in evidence"

/-- This check remains independent of the producer and its search settings. -/
def verify (r : Request) (c : Response) : Bool :=
  validRequest r && validResponse r c &&
    CertificateProducer.accept (graph r) r.result r.program r.claims c.certificate r.start r.inputs

def verifyJson (request evidence : Json) : Except String Unit :=
  match decodeRequest request with
  | .error e => .error e
  | .ok r => match decodeResponse r evidence with
    | .error e => .error e
    | .ok c => if verify r c then .ok () else
        .error "the certificate does not justify the actual program and supplied claims"

/-- Acceptance of JSON binds the theorem to the two decoded input objects. -/
theorem verifyJson_checked {request evidence : Json}
    (h : verifyJson request evidence = .ok ()) :
    ∃ r c, decodeRequest request = .ok r ∧ decodeResponse r evidence = .ok c ∧ verify r c = true := by
  unfold verifyJson at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · exact ⟨_,_,by assumption,by assumption,by assumption⟩
      · contradiction

/-- Produce and serialize, then pass through the same independent JSON consumer.
Fuel bounds search only; it is not part of the certified request. -/
def produceJson (request : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat) := [])
    (known : List (ProgramCertificates.Evidence Nat) := []) : Except String Json := do
  let r ← decodeRequest request
  let C ← match produce (graph r) (List.range r.types.length) fuel
      r.result r.program r.claims r.start [] r.inputs suggestions known with
    | .ok c => pure c
    | .error e => throw s!"evidence search failed (unsupported or unjustified): {reprStr e}"
  let response := toJson (Response.mk 2 C)
  verifyJson request response
  return response

theorem verify_safe {r : Request} {c : Response} (hc : verify r c = true) (n W h ρ)
    (he : EnvOk (graph r) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph r.program (meaning (graph r) r.result) n W h (.at r.start ρ) := by
  simp only [verify, Bool.and_eq_true] at hc
  exact CertificateProducer.accepted_from_inputs hc.2 n W h ρ he hw hh

/-- Empty input contracts retain the closed-invocation corollary. -/
theorem verify_closed_safe {r : Request} {c : Response}
    (hc : verify r c = true) (hi : r.inputs = []) (n : Nat) :
    SafeGraph r.program (meaning (graph r) r.result) n (ofList []) []
      (.at r.start (fun _ => .nul)) := by
  apply verify_safe hc n _ [] _ _ WorldAdm_nil (emptyHeapOk n)
  rw [hi]
  exact ⟨fun _ => trivial, by simp⟩

theorem verify_claims {r : Request} {c : Response} (hc : verify r c = true) :
    c.certificate.map signature = r.claims := by
  simp only [verify, Bool.and_eq_true] at hc
  exact accept_claims hc.2

/-- The JSON entry point certifies its decoded request at every budget, while
retaining exact claim identity. Source meaning is a separate extraction obligation. -/
theorem verifyJson_safe {request evidence : Json}
    (h : verifyJson request evidence = .ok ()) :
    ∃ r c, decodeRequest request = .ok r ∧ decodeResponse r evidence = .ok c ∧
      c.certificate.map signature = r.claims ∧
      ∀ n W h ρ, EnvOk (graph r) r.inputs ρ n W → WorldAdm W → HeapOk n W h →
        SafeGraph r.program (meaning (graph r) r.result) n W h (.at r.start ρ) := by
  obtain ⟨r,c,hr,hc,hv⟩ := verifyJson_checked h
  exact ⟨r,c,hr,hc,verify_claims hv,verify_safe hv⟩

#print axioms verifyJson_safe
#print axioms verifyJson_checked
#print axioms verify_closed_safe
#print axioms verify_safe
#print axioms verify_claims
end Verification.ExperimentState.RequestJson
