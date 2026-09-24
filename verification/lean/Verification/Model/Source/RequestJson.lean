import Lean.Data.Json
import Verification.Model.Programs.CertificateProducer

/-! In-memory JSON boundary for the stateful consumer. A request and its
evidence are separate inputs. This is a calculus protocol, not a decoder for
SKJS types or a TypeScript extractor. No unsupported type is approximated.
`decodeStrict` requires every field and rejects any other, so a document either
has the current shape or is refused. -/
namespace Verification.Model.RequestJson
open Lean ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open ProgramCertificates PointClaims ControlFlow CertificateProducer

/-- A string key is its JSON string, so a document naming only string keys
reads as it always has; a symbol key is `{"symbol": id}`. -/
instance : ToJson PropKey where
  toJson
    | .str name => .str name
    | .sym id => Json.mkObj [("symbol", toJson id)]

instance : FromJson PropKey where
  fromJson?
    | .str name => .ok (.str name)
    | j => do
      let fields ← j.getObj?
      if fields.size != 1 then throw "a symbol key has exactly the field 'symbol'"
      return .sym (← (← j.getObjVal? "symbol").getNat?)

deriving instance ToJson, FromJson for Tag
deriving instance ToJson, FromJson for Arith
deriving instance ToJson, FromJson for Invoke
deriving instance ToJson, FromJson for Tm, CallCode

/-- A closure's kind is left out of its JSON when it is `call`, the kind of
every arrow and method: that is the one spelling of it, so strict decoding,
which re-encodes and compares, refuses an explicit `"call"`, and a closure
without it reads as it always has. Closures nest anywhere in a term, so the
spelling applies at every depth. -/
private partial def closureKinds (restore : Bool) : Json → Json
  | .arr xs => .arr (xs.map (closureKinds restore))
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      let v := closureKinds restore v
      if k != "closure" then (k, v) else
      match v with
      | .obj fields =>
        if restore then
          if fields.contains "kind" then (k, v) else (k, v.setObjVal! "kind" (toJson Invoke.call))
        else if (v.getObjVal? "kind").toOption == some (toJson Invoke.call) then
          (k, Json.mkObj (fields.toArray.toList.filter (·.1 != "kind")))
        else (k, v)
      | _ => (k, v))
  | j => j

private def derivedTmToJson : Tm → Json := toJson
private def derivedTmFromJson : Json → Except String Tm := fromJson?

instance (priority := high) : ToJson Tm := ⟨fun t => closureKinds false (derivedTmToJson t)⟩
instance (priority := high) : FromJson Tm := ⟨fun j => derivedTmFromJson (closureKinds true j)⟩
deriving instance ToJson, FromJson for PositiveNormalization.Tuple
deriving instance ToJson, FromJson for Clause

/-- The clause fields that are left out of JSON when empty: a call clause's
variadic signatures and a record's optional fields. Absence is the one
spelling of none, so strict decoding, which re-encodes and compares, still
refuses an explicit empty list, and a clause without them reads as it always
has. -/
private def omittedWhenEmpty : List (String × String) :=
  [("arrs", "variadic"), ("callable", "variadic"), ("refs", "optional"), ("dict", "optional")]

private def withoutEmptyVariadic (j : Json) : Json :=
  omittedWhenEmpty.foldl (fun j (key, name) =>
    match j.getObjVal? key with
    | .ok body@(.obj _) =>
      match body.getObjVal? name with
      | .ok (.arr xs) =>
        if xs.isEmpty then
          let fields := match body.getObj? with
            | .ok kvs => kvs.toArray.toList.filter (·.1 != name)
            | .error _ => []
          j.setObjVal! key (Json.mkObj fields)
        else j
      | _ => j
    | _ => j) j

private def withEmptyVariadic (j : Json) : Json :=
  omittedWhenEmpty.foldl (fun j (key, name) =>
    match j.getObjVal? key with
    | .ok body@(.obj _) =>
      if (body.getObjVal? name).toOption.isSome then j
      else j.setObjVal! key (body.setObjVal! name (.arr #[]))
    | _ => j) j

private def derivedClauseToJson [ToJson α] : Clause α → Json := toJson
private def derivedClauseFromJson [FromJson α] : Json → Except String (Clause α) := fromJson?

instance (priority := high) [ToJson α] : ToJson (Clause α) :=
  ⟨fun c => withoutEmptyVariadic (derivedClauseToJson c)⟩
instance (priority := high) [FromJson α] : FromJson (Clause α) :=
  ⟨fun j => derivedClauseFromJson (withEmptyVariadic j)⟩
deriving instance ToJson, FromJson for Target
deriving instance ToJson, FromJson for Continuation
deriving instance ToJson, FromJson for Node
deriving instance ToJson, FromJson for PositiveCertificates.ArrowCert
deriving instance ToJson, FromJson for PositiveCertificates.Certificate
deriving instance ToJson, FromJson for PositiveCertificates.Proof
deriving instance ToJson, FromJson for Sequent
deriving instance ToJson, FromJson for Rule
deriving instance ToJson, FromJson for ProgramCertificates.Evidence
deriving instance ToJson, FromJson for HeapFacts.Atom
deriving instance ToJson, FromJson for HeapFacts.Fact
deriving instance ToJson, FromJson for HeapLinks.Link
deriving instance ToJson, FromJson for HeapKnowledge.Knowledge
deriving instance ToJson, FromJson for HeapExpressionRules.StepEvidence
deriving instance ToJson, FromJson for NodeEvidence
deriving instance ToJson, FromJson for PointClaim

structure Request where
  types : List (List (Clause (List Nat)))
  program : Program
  claims : List (PointClaim Nat)
  result : Ty Nat
  start : Nat
  /-- External argument contract, in slot order; independent of point claims. -/
  inputs : List (Ty Nat)
  deriving ToJson, FromJson

structure Response where
  certificate : ControlFlow.Certificate Nat
  deriving ToJson, FromJson

def graph (r : Request) : NormalGraph Nat := .ofRows fun i => r.types[i]?.getD []

def validTy (bound : Nat) (A : Ty Nat) : Bool := A.all (fun i => i < bound)

def clauseTypes : Clause (Ty Nat) → List (Ty Nat)
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _ | .bigint | .symbol
  | .top => []
  | .list a bs => (a :: bs).flatMap fun t => t.required ++ t.optional ++ t.rest.toList
  | .refs A bs vs os => A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ vs.map Prod.snd ++
      os.map Prod.snd
  | .dict A bs vs ds os => A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ vs.map Prod.snd ++ ds ++
      os.map Prod.snd
  | .arrs L S => L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
      S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
  | .callable A bs L S =>
      A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
        S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
  | .ctors L => L.flatMap fun p => p.1 ++ [p.2]

def validClaim (bound : Nat) (c : PointClaim Nat) : Bool :=
  (c.type :: c.context).all (validTy bound)

/-- The total Lean graph's out-of-range default must not become an accidental
meaning for an invalid serialized type reference. -/
def validRequest (r : Request) : Bool :=
  (r.types.flatMap id |>.flatMap clauseTypes).all (validTy r.types.length) &&
  r.claims.all (validClaim r.types.length) && validTy r.types.length r.result &&
  r.inputs.all (validTy r.types.length)

def arrowTypes : PositiveCertificates.ArrowCert Nat → List (Ty Nat)
  | .empty | .emptyRecv => []
  | .source p => p.1 :: p.2.1 ++ [p.2.2]
  | .rest s => s.1 :: s.2.1 ++ [s.2.2.1, s.2.2.2]
  | .union pre a b suffix l r => pre ++ [a,b] ++ suffix ++ arrowTypes l ++ arrowTypes r
  | .recvUnion a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)
  | .combine a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)

def proofTypes : PositiveCertificates.Proof Nat → List (Ty Nat)
  | .subset => []
  | .trans middle l r => middle :: (proofTypes l ++ proofTypes r)
  | .core c => c.table.flatMap (fun p => [p.1,p.2]) ++ c.arrows.flatMap (fun e =>
      e.1.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++ e.2.1.1 :: e.2.1.2.1 ++ [e.2.1.2.2] ++
        arrowTypes e.2.2)

def validEvidence (bound : Nat) : ProgramCertificates.Evidence Nat → Bool
  | .node j r ps =>
    (j.type :: j.context).all (validTy bound) &&
    (match r with
      | .sub p => (proofTypes p).all (validTy bound)
      | .ifBoolVar T F => validTy bound T && validTy bound F
      | .funRest As | .makeCallableRest As => As.all (validTy bound)
      | .callRest _ _ _ E => validTy bound E
      | .arrCopy E => validTy bound E
      | .elemOpt U | .elemAny U => validTy bound U
      | _ => true) &&
    ps.attach.all (fun p => validEvidence bound p.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

def validEffect (bound : Nat) : HeapExpressionRules.StepEvidence Nat → Bool
  | .typedRead _ B e => (B.map Prod.snd).all (validTy bound) && validEvidence bound e
  | .ordinary e | .pure e | .created e | .allocated e | .written _ _ _ e => validEvidence bound e
  | .observedRead _ _ | .knownValue _ _ => true

def validResponse (r : Request) (c : Response) : Bool :=
  c.certificate.all (fun n =>
    validEvidence r.types.length n.expression &&
    (n.effect.map (validEffect r.types.length)).getD true &&
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
  throw "unknown fields or missing explicit fields in the calculus protocol"

def decodeRequest (j : Json) : Except String Request := do
  let r ← decodeStrict j
  if validRequest r then return r
  throw "out-of-range type label in request"

def decodeResponse (r : Request) (j : Json) : Except String Response := do
  let c ← decodeStrict j
  if validResponse r c then return c
  throw "out-of-range type label in evidence"

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

/-! ## Source maps

A source map says how to describe the graph in the words of the source it was
lowered from: one entry per graph label, and within an entry one descriptor per
context binding. Lowering is the only pass that knows both sides, so it is the
only pass that can record this.

Source maps are explanatory. They have no decoder, never reach a request or a
certificate, and cannot affect acceptance; a wrong descriptor mislabels a
message and nothing else. -/

/-- How one context binding is named in the source: a source binding it is
addressable by, the expression whose value it holds, or both. At least one is
present — a context this cannot describe is an extraction error, not a slot
number shown to a reader. -/
structure Descriptor where
  name : String := ""
  span : Option (Nat × Nat) := none
  deriving ToJson, Repr, DecidableEq

def Descriptor.describes (d : Descriptor) : Bool := d.name != "" || d.span.isSome

/-- One graph label's source map entry. `context` runs in context order. -/
structure SourceMapEntry where
  pos : Nat × Nat
  role : String := "node-typing"
  environmentStart : Option Nat := none
  context : List Descriptor := []
  deriving ToJson

/-- The source map for a whole graph: one entry per label, absent where a node
has no source counterpart. -/
abbrev SourceMap := List (Option SourceMapEntry)

/-- One machine-readable record on stderr, following the human-readable error.
This transport leaves successful evidence JSON and the proof protocol unchanged. -/
def withDiagnostic (message : String) (fields : List (String × Json)) : String :=
  message ++ "\nobligation-diagnostic: " ++ (Json.mkObj fields).compress

def failureDiagnostic (r : Request) (fuel : Nat)
    (sourceMap : SourceMap) (e : Failure)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) : List (String × Json) := Id.run do
  let atNode := fun l => Json.mkObj [
    ("label",toJson l), ("sourceMap",toJson ((sourceMap[l]?).bind id)),
    ("node",toJson r.program[l]?), ("claim",toJson r.claims[l]?),
    ("requiredKnowledge",toJson (requirements.lookup l))]
  let phase := match e with
    | .rejected => "certificate-check"
    | .claimCount => "request-validation"
    | _ => "proof-search"
  let common := [("phase",toJson phase),("outcome",toJson "not-established"),
    ("fuel",toJson fuel),("types",toJson r.types),("requiredResult",toJson r.result)]
  match e with
  | .expression label =>
    let goal := do
      let node ← r.program[label]?
      let c ← r.claims[label]?
      pure (Sequent.mk c.context node.expression c.type)
    return common ++ [("kind",toJson "node-typing"),("id",toJson s!"node:{label}"),
      ("source",atNode label),("sequent",toJson goal)]
  | .edge source destination index =>
    let transfer := do
      let node ← r.program[source]?
      let c ← r.claims[source]?
      let (available, target, observation) ← (match node.continuation with
        | .bind t => some (c.type :: c.context, t, (none : Option Bool))
        | .effect t => some (c.context, t, none)
        | .branch y n => some (c.context, if index == 0 then y else n, none)
        | .branchBind y n => some (c.type :: c.context, if index == 0 then y else n, some (index == 0))
        | .tagBind _ y n => some (c.type :: c.context, if index == 0 then y else n, none)
        | .ret => none)
      pure (Json.mkObj [("available",toJson available),("target",toJson target),
        ("booleanObservation",toJson observation),
        ("tagObservation",match node.continuation with
          | .tagBind t _ _ => Json.mkObj [("test",toJson t),("answer",toJson (index == 0)),("slot",toJson (0 : Nat))]
          | _ => Json.null)])
    return common ++ [("kind",toJson "edge-coverage"),("id",toJson s!"edge:{source}:{index}"),
      ("edgeIndex",toJson index),("source",atNode source),("destination",atNode destination),
      ("transfer",toJson transfer)]
  | _ => return common ++ [("kind",toJson "production-failure"),("failure",toJson (reprStr e))]

/-- Produce and serialize, then pass through the same independent JSON consumer.
Fuel bounds search only; it is not part of the certified request. -/
def produceJson (request : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat) := [])
    (known : List (ProgramCertificates.Evidence Nat) := [])
    (sourceMap : SourceMap := [])
    (searchLabels : Option (List Nat) := none)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := []) : Except String Json := do
  let r ← decodeRequest request
  let C ← match produce (graph r) (searchLabels.getD (List.range r.types.length)) fuel
      r.result r.program r.claims r.start [] r.inputs suggestions known requirements cuts with
    | .ok c => pure c
    | .error e =>
      let location := match e with
        | .expression label => match (sourceMap[label]?).bind id with
          | some o => s!"source expression obligation at [{o.pos.1},{o.pos.2}): "
          | none => ""
        | .edge _ destination _ => match (sourceMap[destination]?).bind id with
          | some o => s!"source incoming edge obligation at [{o.pos.1},{o.pos.2}): "
          | none => ""
        | _ => ""
      throw (withDiagnostic s!"{location}evidence search failed (unsupported or unjustified): {reprStr e}"
        (failureDiagnostic r fuel sourceMap e requirements))
  let response := toJson (Response.mk C)
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
end Verification.Model.RequestJson
