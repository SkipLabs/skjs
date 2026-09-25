import Lean.Data.Json
import Verification.Model.Programs.Parametricity
import Verification.Model.Programs.GraphCode

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
deriving instance ToJson, FromJson for Target
deriving instance ToJson, FromJson for Continuation
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
deriving instance ToJson, FromJson for MethodMembers.Sig
deriving instance ToJson, FromJson for OptionalField
deriving instance ToJson, FromJson for KeyBound
deriving instance ToJson, FromJson for IndexKeys
deriving instance ToJson, FromJson for Clause

/-- The clause fields that are left out of JSON when empty: a call clause's
variadic signatures, a record's optional fields, methods and key bounds, and a
dictionary's writable index contracts.
Absence is the one spelling of none, so strict decoding, which re-encodes and
compares, still refuses an explicit empty list, and a clause without them reads
as it always has. -/
private def omittedWhenEmpty : List (String × String) :=
  [("arrs", "variadic"), ("callable", "variadic"), ("ctors", "variadic"), ("refs", "optional"),
   ("dict", "optional"), ("refs", "methods"), ("dict", "methods"), ("refs", "bounds"),
   ("dict", "bounds"), ("dict", "cells")]

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
instance : ToJson ParameterKind := ⟨fun
  | .value => .str "value"
  | .arguments => .str "arguments"⟩

instance : FromJson ParameterKind := ⟨fun j => do
  match ← j.getStr? with
  | "value" => return .value
  | "arguments" => return .arguments
  | _ => throw "expected parameter kind value or arguments"⟩

/-- A row of a type table: a union of clauses, a scheme row (a generic
callable: its binders and its signatures `(receiver, parameters, result)`), a
parameter row (a scheme's binder), which names its own label, or a meet row (a
value parameter row intersected with clauses, `V & DepSafe`). Only a clause
row has clauses; the graph reads the others as scheme, parameter and meet
rows. -/
inductive Row where
  | clauses (union : List (Clause (List Nat)))
  | scheme (binders : List Nat) (signatures : List (List Nat × List (List Nat) × List Nat))
      (bounds : List (Nat × List Nat))
      (variadic : List (List Nat × List (List Nat) × List Nat × List Nat))
  /-- `name` identifies the binder the row stands for (its spelling, where it
  is declared, and its colour); it carries no meaning. -/
  | param (label : Nat) (name : String) (kind : ParameterKind)
  /-- The parameter row `binder` within the clauses `union`. -/
  | meet (binder : Nat) (union : List (Clause (List Nat)))
  deriving DecidableEq, Repr, Inhabited

instance : Coe (List (Clause (List Nat))) Row := ⟨.clauses⟩
instance : Coe (List (List (Clause (List Nat)))) (List Row) := ⟨List.map .clauses⟩

/-- A table of clause rows. -/
def rows (rs : List (List (Clause (List Nat)))) : List Row := rs.map .clauses

/-- A row's clauses: none unless it is a clause row. -/
def Row.union : Row → List (Clause (List Nat))
  | .clauses cs => cs
  | _ => []

/-- A clause row is spelled as its array of clauses, as every row was before
scheme rows; a scheme row as
`{"scheme": {"binders", "signatures", "bounds", "variadic"}}`, its bounds and
its variadic signatures left out when there are none, a parameter row as
`{"param": label, "name": name, "kind": "value" | "arguments"}`, and a meet
row as `{"meet": binder, "clauses": [...]}`. -/
instance : ToJson Row := ⟨fun
  | .clauses cs => toJson cs
  | .scheme bs sigs bounds rests => Json.mkObj [("scheme",
      Json.mkObj ([("binders", toJson bs), ("signatures", toJson sigs)] ++
        (if bounds.isEmpty then [] else [("bounds", toJson bounds)]) ++
        (if rests.isEmpty then [] else [("variadic", toJson rests)])))]
  | .param l n k => Json.mkObj [("param", toJson l), ("name", toJson n), ("kind", toJson k)]
  | .meet p cs => Json.mkObj [("meet", toJson p), ("clauses", toJson cs)]⟩

instance : FromJson Row := ⟨fun j =>
  match j with
  | .arr _ => Row.clauses <$> fromJson? j
  | _ => match j.getObjVal? "scheme", j.getObjVal? "param", j.getObjVal? "meet" with
    | .error _, .error _, .ok p => do
      return .meet (← fromJson? p) (← fromJson? (← j.getObjVal? "clauses"))
    | .ok b, .error _, .error _ => do
      return .scheme (← fromJson? (← b.getObjVal? "binders"))
        (← fromJson? (← b.getObjVal? "signatures"))
        (← match b.getObjVal? "bounds" with
          | .ok v => fromJson? v
          | .error _ => pure [])
        (← match b.getObjVal? "variadic" with
          | .ok v => fromJson? v
          | .error _ => pure [])
    | .error _, .ok l, .error _ => do
      return .param (← fromJson? l) (← fromJson? (← j.getObjVal? "name"))
        (← fromJson? (← j.getObjVal? "kind"))
    | _, _, _ => .error "expected a clause array, a scheme row, a parameter row or a meet row"⟩

/-- The graph a table of rows denotes. Its rows are read by index at every
step of search and checking, so the table is copied into an array once, when
the graph is built: a lookup is then constant time, not a walk down the list.
-/
def tableGraph (T : List Row) : NormalGraph Nat :=
  let A := T.toArray
  { rows i := match A[i]? with
      | some r => r.union
      | none => []
    schemes i := match A[i]? with
      | some (.scheme bs sigs bounds rests) => some ⟨bs, sigs, bounds, rests⟩
      | _ => none
    parameterKinds i := match A[i]? with
      | some (.param _ _ k) => some k
      | _ => none
    meets i := match A[i]? with
      | some (.meet p cs) => some (p, cs)
      | _ => none }

@[simp] theorem tableGraph_clauses_row {T : List Row} {i : Nat} {cs : List (Clause (List Nat))}
    (h : T[i]? = some (.clauses cs)) : (tableGraph T).plain i = true ∧ tableGraph T i = cs := by
  simp [tableGraph, NormalGraph.params, NormalGraph.plain, NormalGraph.clauses, h, Row.union]

deriving instance ToJson, FromJson for Node
deriving instance ToJson, FromJson for PositiveCertificates.ArrowCert
deriving instance ToJson, FromJson for PositiveCertificates.Certificate
deriving instance ToJson, FromJson for PositiveCertificates.Instance
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
deriving instance ToJson, FromJson for CodeEntry

/-- Graph code a request creates, at one signature it offers, with the point
claims of its graph. Nested code comes before the code creating it. -/
structure CodeRequest where
  entry : CodeEntry Nat
  claims : List (PointClaim Nat)
  deriving ToJson, FromJson

structure Request where
  types : List Row
  program : Program
  claims : List (PointClaim Nat)
  result : Ty Nat
  start : Nat
  /-- External argument contract, in slot order; independent of point claims. -/
  inputs : List (Ty Nat)
  /-- The graph code the program creates, each at each signature it offers. -/
  codes : List CodeRequest := []
  deriving ToJson, FromJson

structure Response where
  certificate : ControlFlow.Certificate Nat
  /-- One certificate per code request, in its order. -/
  codes : List (ControlFlow.Certificate Nat) := []
  deriving ToJson, FromJson

def graph (r : Request) : NormalGraph Nat := tableGraph r.types

def validTy (bound : Nat) (A : Ty Nat) : Bool := A.all (fun i => i < bound)

def clauseTypes : Clause (Ty Nat) → List (Ty Nat)
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _ | .bigint | .bigintLit _ | .symbol
  | .top => []
  | .list a bs => (a :: bs).flatMap fun t => t.required ++ t.optional ++ t.rest.toList
  | .pack a bs => (a :: bs).flatMap fun t => t.required ++ t.optional ++ t.rest.toList
  | .refs A bs vs os ms _ => A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ vs.map Prod.snd ++
      os.map (·.type) ++ ms.flatMap MethodMembers.Sig.operands
  | .dict A bs vs ds os ms _ cs => A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ vs.map Prod.snd ++
      ds.map Prod.snd ++ os.map (·.type) ++ ms.flatMap MethodMembers.Sig.operands ++ cs.map Prod.snd

  | .arrs L S => L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
      S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
  | .callable A bs L S =>
      A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
        S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
  | .ctors L S => L.flatMap (fun p => p.1 ++ [p.2]) ++ S.flatMap fun p => p.1 ++ [p.2.1, p.2.2]

def validClaim (bound : Nat) (c : PointClaim Nat) : Bool :=
  (c.type :: c.context).all (validTy bound)

/-- The labels a row names. -/
def rowTypes : Row → List (Ty Nat)
  | .clauses cs => cs.flatMap clauseTypes
  | .scheme bs sigs bounds rests => bs :: (sigs.flatMap fun p => p.1 :: p.2.2 :: p.2.1) ++
      bounds.map (fun b => b.1 :: b.2) ++
      rests.flatMap fun p => p.1 :: p.2.2.1 :: p.2.2.2 :: p.2.1
  | .param _ _ _ => []
  | .meet p cs => [p] :: cs.flatMap clauseTypes

/-- Every label a row names indexes the table; a parameter row names itself;
a scheme's binders are parameter rows, and a meet row's is a value one. -/
def validRows (T : List Row) : Bool :=
  (T.flatMap rowTypes).all (validTy T.length) &&
  (List.range T.length).all fun i => match T[i]? with
    | some (.param l _ _) => l == i
    | some (.scheme bs _ _ _) => bs.all fun b => match T[b]? with
      | some (.param _ _ _) => true
      | _ => false
    | some (.meet p _) => match T[p]? with
      | some (.param _ _ .value) => true
      | _ => false
    | _ => true

/-- The total Lean graph's out-of-range default must not become an accidental
meaning for an invalid serialized type reference. -/
def validRequest (r : Request) : Bool :=
  validRows r.types &&
  r.claims.all (validClaim r.types.length) && validTy r.types.length r.result &&
  r.inputs.all (validTy r.types.length) &&
  r.codes.all fun q => q.claims.all (validClaim r.types.length) &&
    (q.entry.row.1 :: q.entry.row.2.2 :: q.entry.row.2.1 ++ q.entry.captures).all
      (validTy r.types.length)

def arrowTypes : PositiveCertificates.ArrowCert Nat → List (Ty Nat)
  | .empty | .emptyRecv => []
  | .source p => p.1 :: p.2.1 ++ [p.2.2]
  | .rest s => s.1 :: s.2.1 ++ [s.2.2.1, s.2.2.2]
  | .union pre a b suffix l r => pre ++ [a,b] ++ suffix ++ arrowTypes l ++ arrowTypes r
  | .recvUnion a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)
  | .combine a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)

def certificateTypes (c : PositiveCertificates.Certificate Nat) : List (Ty Nat) :=
  c.table.flatMap (fun p => [p.1,p.2]) ++ c.arrows.flatMap (fun e =>
    e.1.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++ e.2.1.1 :: e.2.1.2.1 ++ [e.2.1.2.2] ++
      arrowTypes e.2.2)

def instanceTypes (c : PositiveCertificates.Instance Nat) : List (Ty Nat) :=
  c.domain :: c.instances ++ c.free.flatMap (fun p => [[p.1], p.2]) ++
    c.bounds.flatMap (fun c => match c with
      | some cert => certificateTypes cert
      | none => []) ++
    c.table.flatMap (fun e => [e.1] :: e.2.2 :: e.2.1.flatMap (fun p => [[p.1], p.2]))

def proofTypes : PositiveCertificates.Proof Nat → List (Ty Nat)
  | .subset => []
  | .trans middle l r => middle :: (proofTypes l ++ proofTypes r)
  | .inst c => instanceTypes c
  | .gen D V U p => D :: U :: V.flatMap (fun p => [[p.1], p.2]) ++ proofTypes p
  | .table tbl D V => D :: V.flatMap (fun p => [[p.1], p.2]) ++
      tbl.flatMap (fun e => [e.1] :: e.2.2 :: e.2.1.flatMap (fun p => [[p.1], p.2]))
  | .core c ks => certificateTypes c ++ ks.flatMap (fun k => k.1 ::
      k.2.1.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
      k.2.2.1.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2]) ++ instanceTypes k.2.2.2)

def validEvidence (bound : Nat) : ProgramCertificates.Evidence Nat → Bool
  | .node j r ps =>
    (j.type :: j.context).all (validTy bound) &&
    (match r with
      | .sub p => (proofTypes p).all (validTy bound)
      | .bindMember ps => ps.all fun p =>
          (p.1.flatMap proofTypes ++ proofTypes p.2).all (validTy bound)
      | .ifBoolVar T F => validTy bound T && validTy bound F
      | .funRest As | .makeCallableRest As => As.all (validTy bound)
      | .callRest _ _ _ E => validTy bound E
      | .arrCopy E => validTy bound E
      | .readProto P => validTy bound P
      | .elemOpt U | .elemAny U => validTy bound U
      | .elemStr T U => validTy bound T && validTy bound U
      | _ => true) &&
    ps.attach.all (fun p => validEvidence bound p.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

def validEffect (bound : Nat) : HeapExpressionRules.StepEvidence Nat → Bool
  | .ordinary e | .pure e | .created e | .allocated e | .typedRead _ e | .written _ _ _ e =>
    validEvidence bound e
  | .observedRead _ _ | .knownValue _ _ => true

def validCertificate (bound : Nat) (C : ControlFlow.Certificate Nat) : Bool :=
  C.all (fun n =>
    validEvidence bound n.expression &&
    (n.effect.map (validEffect bound)).getD true &&
    (n.edges.flatMap id |>.flatMap proofTypes).all (validTy bound))

def validResponse (r : Request) (c : Response) : Bool :=
  validCertificate r.types.length c.certificate && c.codes.all (validCertificate r.types.length)

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

/-- The request's graph code, checked in order against its claims, as a table
of what was checked (`GraphCode.checkCodes`). -/
def codeTable (r : Request) (c : Response) : Option (List (CodeEntry Nat)) :=
  if r.codes.length == c.codes.length &&
      (r.codes.zip c.codes).all (fun (q, C) => C.map signature == q.claims) then
    GraphCode.checkCodes (graph r) ((r.codes.map (·.entry)).zip c.codes)
  else none

/-- This check remains independent of the producer and its search settings. -/
def verify (r : Request) (c : Response) : Bool :=
  validRequest r && validResponse r c &&
    match codeTable r c with
    | some table => CertificateProducer.accept (graph r) r.result r.program r.claims c.certificate
        r.start r.inputs (GraphCode.admits table)
    | none => false

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

/-- A code request as a request of its own: its graph, from the frame its
signature describes, at the signature's result. What it may create is the
table checked before it, not part of this request. -/
def CodeRequest.asRequest (r : Request) (q : CodeRequest) : Request :=
  { types := r.types, program := GraphCode.program q.entry.exprs q.entry.conts, claims := q.claims,
    result := q.entry.row.2.2, start := q.entry.start,
    inputs := bodyFrame q.entry.arity q.entry.row q.entry.captures, codes := [] }

/-- Search one graph's certificate, the codes of `table` admitted. -/
def produceGraph (r : Request) (fuel : Nat) (labels : List Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat)) (known : List (ProgramCertificates.Evidence Nat))
    (sourceMap : SourceMap) (requirements : List (Nat × HeapKnowledge.Knowledge)) (cuts : List Nat)
    (table : List (CodeEntry Nat)) : Except String (ControlFlow.Certificate Nat) :=
  match produce (graph r) labels fuel r.result r.program r.claims r.start [] r.inputs suggestions known
      requirements cuts (GraphCode.admits table) with
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
    -- Name what could not be established; the structured record below says
    -- with which claims, and the reader phrases it in source terms.
    let what := match e with
      | .expression label => match (sourceMap[label]?).bind id with
        | some o => s!"no derivation of its {o.role} claim"
        | none => s!"no derivation of the claim of node {label}"
      | .edge source _ _ => s!"the edge from node {source} does not establish the claims at this point"
      | _ => reprStr e
    throw (withDiagnostic s!"{location}evidence search failed: {what}"
      (failureDiagnostic r fuel sourceMap e requirements))

/-- What search knows of a code request beyond the request: its source map, its
statement entries' required knowledge and its cuts, as for a unit. -/
structure CodeHints where
  sourceMap : SourceMap := []
  requirements : List (Nat × HeapKnowledge.Knowledge) := []
  cuts : List Nat := []

/-- Produce and serialize, then pass through the same independent JSON consumer.
Fuel bounds search only; it is not part of the certified request. -/
def produceJson (request : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat) := [])
    (known : List (ProgramCertificates.Evidence Nat) := [])
    (sourceMap : SourceMap := [])
    (searchLabels : Option (List Nat) := none)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codeHints : List CodeHints := []) : Except String Json := do
  let r ← decodeRequest request
  let labels := searchLabels.getD (List.range r.types.length)
  -- Each code against the table of those before it, as `codeTable` checks.
  let mut table : List (CodeEntry Nat) := []
  let mut certificates : List (ControlFlow.Certificate Nat) := []
  for (q, i) in r.codes.zipIdx do
    let hints := (codeHints[i]?).getD {}
    let C ← produceGraph (q.asRequest r) fuel labels suggestions known hints.sourceMap
      hints.requirements hints.cuts table
    certificates := certificates ++ [C]
    table := table ++ [q.entry]
  let C ← produceGraph r fuel labels suggestions known sourceMap requirements cuts table
  let response := toJson (Response.mk C certificates)
  verifyJson request response
  return response

theorem verify_safe {r : Request} {c : Response} (hc : verify r c = true) (n W h ρ)
    (he : EnvOk (graph r) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph r.program (meaning (graph r) r.result) n W h (.at r.start ρ) := by
  simp only [verify, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i table ht
    have hsound : ProgramCertificates.CodesSound (graph r) (GraphCode.admits table) := by
      unfold codeTable at ht
      split at ht
      · exact GraphCode.checkCodes_sound ht
      · contradiction
    exact CertificateProducer.accepted_from_inputs hx n W h ρ he hw hh hsound
  · contradiction

/-- Accepted evidence is safe at every assignment of the request graph's
parameter rows (`Parametricity.accepted_at`): a request whose inputs and
result mention a generic body's binders, read as parameter rows, is safe at
every instantiation of them. At the graph's own assignment this is
`verify_safe`. -/
theorem verify_safe_at {r : Request} {c : Response} (hc : verify r c = true)
    (η : MixedAssignment Nat) (n W h ρ)
    (he : EnvOk (reassign (graph r) η) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph r.program (meaning (reassign (graph r) η) r.result) n W h (.at r.start ρ) := by
  simp only [verify, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i table ht
    have hsound : ProgramCertificates.CodesSound (reassign (graph r) η) (GraphCode.admits table) := by
      unfold codeTable at ht
      split at ht
      · rw [← GraphCode.checkCodes_reassign (graph r) η] at ht
        exact GraphCode.checkCodes_sound ht
      · contradiction
    exact Parametricity.accepted_at hx η n W h ρ he hw hh hsound
  · contradiction

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
  have hx := hc.2
  split at hx
  · exact accept_claims hx
  · contradiction

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
#print axioms verify_safe_at
#print axioms verify_claims
end Verification.Model.RequestJson
