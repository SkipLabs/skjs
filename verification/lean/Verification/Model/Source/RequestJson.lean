import Lean.Data.Json
import Verification.Model.Types.GraphRows
import Verification.Model.Programs.Parametricity
import Verification.Model.Programs.GraphCode
import Verification.Model.Source.LabelStore

/-! In-memory JSON boundary for the stateful consumer. A request and its
evidence are separate inputs. This is a calculus protocol, not a decoder for
SKJS types or a TypeScript extractor. No unsupported type is approximated.
`decodeStrict` requires every field and rejects any other, so a document either
has the current shape or is refused. -/
namespace Verification.Model.RequestJson
open Lean ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open ProgramCertificates PointClaims ControlFlow CertificateProducer
open CallEffects (Arrow RestArrow Contract Effect)
open LabelStore

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

/-- A code's kind is left out of its JSON when it is `call`, the kind of every
arrow and method, and graph code's rest when it collects none: that is the one
spelling of each, so strict decoding, which re-encodes and compares, refuses an
explicit `"call"` or `false`, and a code without them reads as it always has.
Code nests anywhere in a term, so the spelling applies at every depth. -/
private partial def closureKinds (restore : Bool) : Json → Json
  | .arr xs => .arr (xs.map (closureKinds restore))
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      let v := closureKinds restore v
      let defaults : List (String × Json) := match k with
        | "closure" => [("kind", toJson Invoke.call)]
        | "graph" => [("kind", toJson Invoke.call), ("rest", toJson false)]
        | _ => []
      match v with
      | .obj fields =>
        (k, defaults.foldl (fun v (field, dflt) =>
          if restore then
            if fields.contains field then v else v.setObjVal! field dflt
          else if (v.getObjVal? field).toOption == some dflt then
            match v with
            | .obj fs => Json.mkObj (fs.toArray.toList.filter (·.1 != field))
            | v => v
          else v) v)
      | _ => (k, v))
  | j => j

private def derivedTmToJson : Tm → Json := toJson
private def derivedTmFromJson : Json → Except String Tm := fromJson?

instance (priority := high) : ToJson Tm := ⟨fun t => closureKinds false (derivedTmToJson t)⟩
instance (priority := high) : FromJson Tm := ⟨fun j => derivedTmFromJson (closureKinds true j)⟩
deriving instance ToJson, FromJson for ArrayPresence
deriving instance ToJson, FromJson for PositiveNormalization.Tuple
deriving instance ToJson, FromJson for Effect
deriving instance ToJson, FromJson for Contract
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
abbrev Row := GraphRow Nat

instance : Coe (List (Clause (List Nat))) Row := ⟨.clauses⟩
instance : Coe (List (List (Clause (List Nat)))) (List Row) := ⟨List.map .clauses⟩

/-- A table of clause rows. -/
def rows (rs : List (List (Clause (List Nat)))) : List Row := rs.map .clauses

/-- A clause row is spelled as its array of clauses, as every row was before
scheme rows; a scheme row as
`{"scheme": {"binders", "signatures", "bounds", "variadic"}}`, its bounds and
its variadic signatures left out when there are none, a parameter row as
`{"param": label, "name": name, "kind": "value" | "arguments"}`, and a meet
row as `{"meet": binder, "clauses": [...]}`, whatever the labels are. -/
instance [ToJson ι] [ToJson α] : ToJson (GraphRow ι α) := ⟨fun
  | .clauses cs => toJson cs
  | .scheme bs sigs bounds rests => Json.mkObj [("scheme",
      Json.mkObj ([("binders", toJson bs), ("signatures", toJson sigs)] ++
        (if bounds.isEmpty then [] else [("bounds", toJson bounds)]) ++
        (if rests.isEmpty then [] else [("variadic", toJson rests)])))]
  | .param l n k => Json.mkObj [("param", toJson l), ("name", toJson n), ("kind", toJson k)]
  | .meet p cs ps => Json.mkObj ([("meet", toJson p), ("clauses", toJson cs)] ++
      (if ps.isEmpty then [] else [("also", toJson ps)]))⟩

instance [FromJson ι] [FromJson α] : FromJson (GraphRow ι α) := ⟨fun j =>
  match j with
  | .arr _ => GraphRow.clauses <$> fromJson? j
  | _ => match j.getObjVal? "scheme", j.getObjVal? "param", j.getObjVal? "meet" with
    | .error _, .error _, .ok p => do
      return .meet (← fromJson? p) (← fromJson? (← j.getObjVal? "clauses"))
        (← match j.getObjVal? "also" with
          | .ok v => fromJson? v
          | .error _ => pure [])
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

/-- A diagnostic's `types` field, and its `names` field when there are any. -/
def _root_.Verification.Model.LabelStore.Projection.fields {ι : Type} (p : Projection ι) :
    List (String × Json) :=
  ("types", toJson p.rows) :: (if p.names.isEmpty then [] else [("names", toJson p.names)])

/-! ### The realm's arrays -/

/-- A name in double brackets, which the model keeps for itself: the
prototype key and a class's prototype object's own key
(`Fragment.classKeyOf`). -/
def bracketed : PropKey → Bool
  | .str s => s.startsWith "[[" && s.endsWith "]]"
  | .sym _ => false

/-- A key the model keeps for itself: the array store, the prototype, and
every other name in double brackets. -/
def reservedKey (k : PropKey) : Bool :=
  k == CallArguments.arrayStoreField || k == CallArguments.protoField || bracketed k

/-- The row of `ArrayProto`, `Array.prototype`'s contract: the declaration
document of a source with arrays lists it first, so its row follows the four
fixed ones (`DeclarationGraph.prepare` checks this). -/
def arrayProtoLabel : Nat := 4

/-- The keys an ordinary array cannot own: its prototype's declared keys and
`constructor`. The latter preserves the realm's standard species construction.
Sorted, each once, with the model's reserved keys aside. -/
def arrayExcludedKeys (ks : List PropKey) : List PropKey :=
  (((PropKey.str "constructor" :: ks).filter fun k => !reservedKey k).eraseDups).mergeSort PropKey.before

/-- The excluded array keys: `constructor` and the prototype row's fields', views', optional fields'
and methods', the reserved keys aside. -/
def arrayExcludedKeysOf : List (Clause (List ι)) → List PropKey
  | [.refs a bs vs os ms _] =>
    arrayExcludedKeys (((a :: bs).flatten ++ vs).map (·.1) ++ os.map (·.key) ++ ms.map (·.key))
  | _ => arrayExcludedKeys []

/-- An array type's clause: an object owning the store key, holding
`ArrayProto` as a view under the prototype key. -/
def arrayShaped : Clause (List Nat) → Bool
  | .refs a bs vs _ _ _ =>
    ((a :: bs).flatten ++ vs).any (·.1 == CallArguments.arrayStoreField) &&
      vs.any (· == (CallArguments.protoField, [arrayProtoLabel]))
  | _ => false

/-- The realm a table states: where it has an array type, `ArrayProto` is its
row `arrayProtoLabel`, and the keys it provides are that row's. A table without
arrays states none. -/
def tableRealm (T : List Row) : Option (ArrayRealm Nat) :=
  if T.any (fun r => match r with | .clauses cs => cs.any arrayShaped | _ => false) then
    some ⟨[arrayProtoLabel], match T[arrayProtoLabel]? with
      | some (.clauses cs) => arrayExcludedKeysOf cs
      | _ => arrayExcludedKeys []⟩
  else none

/-- The graph a table of rows denotes. Its rows are read by index at every
step of search and checking, so the table is copied into an array once, when
the graph is built: a lookup is then constant time, not a walk down the list.
-/
def tableGraph (T : List Row) : NormalGraph Nat :=
  let A := T.toArray
  NormalGraph.ofRowMap (fun i => A[i]?.getD (.clauses [])) (tableRealm T)

@[simp] theorem tableGraph_clauses_row {T : List Row} {i : Nat} {cs : List (Clause (List Nat))}
    (h : T[i]? = some (.clauses cs)) : (tableGraph T).plain i = true ∧ tableGraph T i = cs := by
  simp [tableGraph, NormalGraph.ofRowMap, NormalGraph.params, NormalGraph.plain, NormalGraph.clauses, h, GraphRow.union]

/-! ### The finite table as a store

A finite table's labels are its row positions, and its first four rows are
the primitives: null, true, false, undefined (`SourceTypes.initial`). -/

instance : Labels Nat where
  toHashable := inferInstance
  toOrd := inferInstance
  toToJson := inferInstance
  toFromJson := inferInstance
  toRepr := inferInstance
  decEq := inferInstance
  nul := 0
  tru := 1
  fls := 2
  undef := 3

/-- A table of rows in label order. -/
abbrev Table := List Row

/-- Every label a row names indexes the table; a parameter row names itself;
a scheme's binders are parameter rows, and a meet row's are value ones. -/
def validRows (T : Table) : Bool :=
  (T.flatMap GraphRow.operands).all (·.all (· < T.length)) &&
  (List.range T.length).all fun i => match T[i]? with
    | some (.param l _ _) => l == i
    | some (.scheme bs _ _ _) => bs.all fun b => match T[b]? with
      | some (.param _ _ _) => true
      | _ => false
    | some (.meet p _ ps) => (p :: ps).all fun q => match T[q]? with
      | some (.param _ _ .value) => true
      | _ => false
    | _ => true

namespace Table

/-- A clause row's label: the first row with exactly these clauses, appended
if there is none. Appending keeps every existing label. -/
def intern (T : Table) (cs : List (Clause (List Nat))) : Table × Nat :=
  let T' := if GraphRow.clauses cs ∈ T then T else T ++ [GraphRow.clauses cs]
  (T', T'.idxOf (GraphRow.clauses cs))

/-- Any row's label: its first occurrence, appended if there is none. -/
def internRow (T : Table) (r : Row) : Table × Nat :=
  match T.idxOf? r with
  | some i => (T, i)
  | none => (T ++ [r], T.length)

/-- The value parameter row that stands for a generic unit's binder `name`:
the table's one value parameter row of that name that no scheme binds, or a
new one. The row carries no meaning of its own: a unit over it is certified at
every assignment of it (`Parametricity.accepted_at`). -/
def binder (T : Table) (name : String) : Except String (Table × Nat) := do
  let schemeBinders := T.flatMap fun
    | .scheme bs .. => bs
    | _ => []
  let named := (List.range T.length).filter fun i => match (T[i]? : Option Row) with
    | some (.param l n .value) => l == i && n == name && !schemeBinders.contains i
    | _ => false
  match named with
  | [l] => return (T, l)
  | [] => return (T ++ [GraphRow.param T.length name .value], T.length)
  | _ => throw s!"two parameter rows stand for the binder '{name}'"

/-- A fresh value parameter row per name, in order. -/
def binders (T : Table) (names : List String) : Table × List Nat :=
  let params := names.zipIdx.map fun (n, i) => (n, T.length + i)
  (T ++ params.map (fun (n, l) => GraphRow.param l n .value), params.map Prod.snd)

end Table

instance : Store Table Nat where
  toToJson := inferInstance
  toFromJson := inferInstance
  graph := tableGraph
  row T i := T[i]?.getD (.clauses [])
  valid T i := i < T.length
  wellFormed := validRows
  labels T := List.range T.length
  bound T := T.length
  arrayProto _ := arrayProtoLabel
  intern := Table.intern
  lookup T cs := T.idxOf? (GraphRow.clauses cs)
  binder := Table.binder
  binders := Table.binders
  bounded T p cs also := Table.internRow T (.meet p cs also)
  scheme T bs sigs bounds rests := (T ++ [GraphRow.scheme bs sigs bounds rests], T.length)
  -- A table is finite already and its labels are positions: a diagnostic
  -- shows all of it, as it is, since a sub-table would renumber its rows.
  project T _ _ := { rows := T, position := id }
  images T := PositiveCertificates.finiteInstanceImages (tableGraph T)
  -- A table names its binders by rows, never by name.
  rebind _ _ l := [l]

@[simp] theorem Table.graph_eq (T : Table) : StoreView.graph T = tableGraph T := rfl
@[simp] theorem Table.nul_eq : (Labels.nul : Nat) = 0 := rfl
@[simp] theorem Table.tru_eq : (Labels.tru : Nat) = 1 := rfl
@[simp] theorem Table.fls_eq : (Labels.fls : Nat) = 2 := rfl
@[simp] theorem Table.undef_eq : (Labels.undef : Nat) = 3 := rfl

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
structure CodeRequest (ι : Type) where
  entry : CodeEntry ι
  claims : List (PointClaim ι)
  deriving ToJson, FromJson

/-- A request over a store `σ` of labels `ι`: its program, point claims,
result and inputs are typed by the store's labels. -/
structure Request (σ ι : Type) where
  types : σ
  program : Program
  claims : List (PointClaim ι)
  result : Ty ι
  start : Nat
  /-- External argument contract, in slot order; independent of point claims. -/
  inputs : List (Ty ι)
  /-- The graph code the program creates, each at each signature it offers. -/
  codes : List (CodeRequest ι) := []
  deriving ToJson, FromJson

structure Response (ι : Type) where
  certificate : ControlFlow.Certificate ι
  /-- One certificate per code request, in its order. -/
  codes : List (ControlFlow.Certificate ι) := []
  deriving ToJson, FromJson

/-- A request's and a response's `codes` are left out when empty. Absence is
the one spelling of none, so strict decoding, which re-encodes and compares,
refuses an explicit empty list, and a request without code reads as none. -/
private def withoutEmptyCodes (j : Json) : Json :=
  match j.getObjVal? "codes", j with
  | .ok (.arr xs), .obj kvs =>
    if xs.isEmpty then Json.mkObj (kvs.toArray.toList.filter (·.1 != "codes")) else j
  | _, _ => j

private def withEmptyCodes (j : Json) : Json :=
  match j, j.getObjVal? "codes" with
  | .obj _, .error _ => j.setObjVal! "codes" (.arr #[])
  | _, _ => j

private def derivedRequestToJson [ToJson σ] [ToJson ι] : Request σ ι → Json := toJson
private def derivedRequestFromJson [FromJson σ] [FromJson ι] : Json → Except String (Request σ ι) :=
  fromJson?
private def derivedResponseToJson [ToJson ι] : Response ι → Json := toJson
private def derivedResponseFromJson [FromJson ι] : Json → Except String (Response ι) := fromJson?

instance (priority := high) [ToJson σ] [ToJson ι] : ToJson (Request σ ι) :=
  ⟨fun r => withoutEmptyCodes (derivedRequestToJson r)⟩
instance (priority := high) [FromJson σ] [FromJson ι] : FromJson (Request σ ι) :=
  ⟨fun j => derivedRequestFromJson (withEmptyCodes j)⟩
instance (priority := high) [ToJson ι] : ToJson (Response ι) :=
  ⟨fun r => withoutEmptyCodes (derivedResponseToJson r)⟩
instance (priority := high) [FromJson ι] : FromJson (Response ι) :=
  ⟨fun j => derivedResponseFromJson (withEmptyCodes j)⟩

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

def graph (r : Request σ ι) : NormalGraph ι := StoreView.graph r.types

def validTy (ok : ι → Bool) (A : Ty ι) : Bool := A.all ok

/-- Use the clause language's operand traversal for boundary validation too. -/
def clauseTypes : Clause (Ty ι) → List (Ty ι) := Clause.operands

def validClaim (ok : ι → Bool) (c : PointClaim ι) : Bool :=
  (c.type :: c.context).all (validTy ok)

/-- The total Lean graph's out-of-range default must not become an accidental
meaning for an invalid serialized type reference. -/
def validRequest (r : Request σ ι) : Bool :=
  let ok := StoreView.valid r.types
  StoreView.wellFormed r.types &&
  r.claims.all (validClaim ok) && validTy ok r.result &&
  r.inputs.all (validTy ok) &&
  r.codes.all fun q => q.claims.all (validClaim ok) &&
    (q.entry.row.operands ++ q.entry.captures ++
      q.entry.store.toList).all
      (validTy ok)

def arrowTypes : PositiveCertificates.ArrowCert ι → List (Ty ι)
  | .empty | .emptyRecv => []
  | .source p => p.operands
  | .rest s => s.operands
  | .union pre a b suffix l r => pre ++ [a,b] ++ suffix ++ arrowTypes l ++ arrowTypes r
  | .recvUnion a b l r => a :: b :: (arrowTypes l ++ arrowTypes r)
  | .combine a b _ _ l r => a :: b :: (arrowTypes l ++ arrowTypes r)

def certificateTypes (c : PositiveCertificates.Certificate ι) : List (Ty ι) :=
  c.table.flatMap (fun p => [p.1,p.2]) ++ c.arrows.flatMap (fun e =>
    e.1.flatMap Arrow.operands ++ e.2.1.operands ++
      arrowTypes e.2.2)

def instanceTypes (c : PositiveCertificates.Instance ι) : List (Ty ι) :=
  c.domain :: c.instances ++ c.free.flatMap (fun p => [[p.1], p.2]) ++
    c.bounds.flatMap (fun c => match c with
      | some cert => certificateTypes cert
      | none => []) ++
    c.table.flatMap (fun e => [e.1] :: e.2.2 :: e.2.1.flatMap (fun p => [[p.1], p.2]))

def proofTypes : PositiveCertificates.Proof ι → List (Ty ι)
  | .subset => []
  | .trans middle l r => middle :: (proofTypes l ++ proofTypes r)
  | .inst c => instanceTypes c
  | .gen D V U p => D :: U :: V.flatMap (fun p => [[p.1], p.2]) ++ proofTypes p
  | .table tbl D V => D :: V.flatMap (fun p => [[p.1], p.2]) ++
      tbl.flatMap (fun e => [e.1] :: e.2.2 :: e.2.1.flatMap (fun p => [[p.1], p.2]))
  | .core c ks => certificateTypes c ++ ks.flatMap (fun k => k.1 ::
      k.2.1.flatMap Arrow.operands ++
      k.2.2.1.flatMap RestArrow.operands ++ instanceTypes k.2.2.2)

def validEvidence (ok : ι → Bool) : ProgramCertificates.Evidence ι → Bool
  | .node j r ps =>
    (j.type :: j.context).all (validTy ok) &&
    (match r with
      | .sub p => (proofTypes p).all (validTy ok)
      | .bindMember ps => ps.all fun p =>
          (p.1.flatMap proofTypes ++ proofTypes p.2).all (validTy ok)
      | .ifBoolVar T F => validTy ok T && validTy ok F
      | .funGraph As | .callableGraph As => As.all (validTy ok)
      | .ctorGraph U => validTy ok U
      | .callRest _ _ _ _ E => validTy ok E
      | .arrCopy E => validTy ok E
      | .readProto P => validTy ok P
      | .elemOpt U | .elemAny U => validTy ok U
      | .elemStr T U => validTy ok T && validTy ok U
      | _ => true) &&
    ps.attach.all (fun p => validEvidence ok p.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

def validEffect (ok : ι → Bool) : HeapExpressionRules.StepEvidence ι → Bool
  | .ordinary e | .pure e | .created e | .allocated e | .typedRead _ e | .written _ _ _ e =>
    validEvidence ok e
  | .slicedRead _ e p => validEvidence ok e && (proofTypes p).all (validTy ok)
  | .observedRead _ _ | .knownValue _ _ => true

def validCertificate (ok : ι → Bool) (C : ControlFlow.Certificate ι) : Bool :=
  C.all (fun n =>
    validEvidence ok n.expression &&
    (n.effect.map (validEffect ok)).getD true &&
    (n.edges.flatMap id |>.flatMap proofTypes).all (validTy ok))

def validResponse (r : Request σ ι) (c : Response ι) : Bool :=
  validCertificate (StoreView.valid r.types) c.certificate &&
    c.codes.all (validCertificate (StoreView.valid r.types))

end

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

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- A request over the store `σ`, which names how its table is spelled. -/
def decodeRequest (σ : Type) [StoreView σ ι] (j : Json) : Except String (Request σ ι) := do
  let r ← decodeStrict j
  if validRequest r then return r
  throw "out-of-range type label in request"

def decodeResponse (r : Request σ ι) (j : Json) : Except String (Response ι) := do
  let c ← decodeStrict j
  if validResponse r c then return c
  throw "out-of-range type label in evidence"

/-- The request's graph code, checked in order against its claims, as a table
of what was checked (`GraphCode.checkCodes`). -/
def codeTable (r : Request σ ι) (c : Response ι) : Option (List (CodeEntry ι)) :=
  if r.codes.length == c.codes.length &&
      (r.codes.zip c.codes).all (fun (q, C) => C.map signature == q.claims) then
    GraphCode.checkCodesUsing (graph r) (StoreView.images r.types) ((r.codes.map (·.entry)).zip c.codes)
  else none

/-- This check remains independent of the producer and its search settings. -/
def verify (r : Request σ ι) (c : Response ι) : Bool :=
  validRequest r && validResponse r c &&
    match codeTable r c with
    | some table => CertificateProducer.acceptUsing (graph r) (StoreView.images r.types) r.result r.program
        r.claims c.certificate
        r.start r.inputs (GraphCode.admits table)
    | none => false

def verifyJson (σ : Type) [StoreView σ ι] (request evidence : Json) : Except String Unit :=
  match decodeRequest σ request with
  | .error e => .error e
  | .ok r => match decodeResponse r evidence with
    | .error e => .error e
    | .ok c => if verify r c then .ok () else
        .error "the certificate does not justify the actual program and supplied claims"

/-- Acceptance of JSON binds the theorem to the two decoded input objects. -/
theorem verifyJson_checked {request evidence : Json}
    (h : verifyJson (ι := ι) σ request evidence = .ok ()) :
    ∃ r c, decodeRequest σ request = .ok r ∧ decodeResponse r evidence = .ok c ∧ verify r c = true := by
  unfold verifyJson at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · exact ⟨_,_,by assumption,by assumption,by assumption⟩
      · contradiction

end

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

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- A point claim as a diagnostic shows it, through the store's projection. -/
def PointClaim.shown (p : Projection ι) (c : PointClaim ι) : PointClaim Nat :=
  ⟨c.context.map p.shown, p.shown c.type⟩

/-- The labels a point claim mentions. -/
def PointClaim.mentions (c : PointClaim ι) : List ι := c.type ++ c.context.flatten

/-- A graph failure as a diagnostic: its types are the store's projection
(`StoreView.project`) onto the labels the record mentions. -/
def failureDiagnostic (r : Request σ ι) (fuel : Nat)
    (sourceMap : SourceMap) (e : Failure)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) : List (String × Json) := Id.run do
  let claimAt := fun l => (r.claims[l]? : Option (PointClaim ι))
  let mentionedAt := fun l => ((claimAt l).map PointClaim.mentions).getD []
  let mentioned := match e with
    | .expression label => mentionedAt label
    | .edge source destination _ => mentionedAt source ++ mentionedAt destination
    | _ => []
  let p := Store.projection r.types (r.result ++ mentioned).eraseDups
  let atNode := fun l => Json.mkObj [
    ("label",toJson l), ("sourceMap",toJson ((sourceMap[l]?).bind id)),
    ("node",toJson r.program[l]?), ("claim",toJson ((claimAt l).map (PointClaim.shown p))),
    ("requiredKnowledge",toJson (requirements.lookup l))]
  let phase := match e with
    | .rejected => "certificate-check"
    | .claimCount => "request-validation"
    | _ => "proof-search"
  let common := [("phase",toJson phase),("outcome",toJson "not-established"),
    ("fuel",toJson fuel),("requiredResult",toJson (p.shown r.result))] ++ p.fields
  match e with
  | .expression label =>
    let goal := do
      let node ← r.program[label]?
      let c ← claimAt label
      pure (Sequent.mk (c.context.map p.shown) node.expression (p.shown c.type))
    return common ++ [("kind",toJson "node-typing"),("id",toJson s!"node:{label}"),
      ("source",atNode label),("sequent",toJson goal)]
  | .edge source destination index =>
    let transfer := do
      let node ← r.program[source]?
      let c := PointClaim.shown p (← claimAt source)
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
def CodeRequest.asRequest (r : Request σ ι) (q : CodeRequest ι) : Request σ ι :=
  { types := r.types, program := GraphCode.program q.entry.exprs q.entry.conts, claims := q.claims,
    result := q.entry.row.result, start := q.entry.start,
    inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.store, codes := [] }

/-- Search one graph's certificate, the codes of `table` admitted. -/
def produceGraph (r : Request σ ι) (fuel : Nat) (labels : List ι)
    (suggestions : List (ProgramCertificates.Sequent ι)) (known : List (ProgramCertificates.Evidence ι))
    (sourceMap : SourceMap) (requirements : List (Nat × HeapKnowledge.Knowledge)) (cuts : List Nat)
    (table : List (CodeEntry ι)) : Except String (ControlFlow.Certificate ι) :=
  match CertificateProducer.produceUsing (graph r) (StoreView.images r.types) labels fuel r.result r.program r.claims r.start [] r.inputs suggestions known
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
def produceJson (σ : Type) [StoreView σ ι] (request : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent ι) := [])
    (known : List (ProgramCertificates.Evidence ι) := [])
    (sourceMap : SourceMap := [])
    (searchLabels : Option (List ι) := none)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codeHints : List CodeHints := []) : Except String Json := do
  let r ← decodeRequest σ request
  let labels := searchLabels.getD (StoreView.labels r.types)
  -- Each code against the table of those before it, as `codeTable` checks.
  let mut table : List (CodeEntry ι) := []
  let mut certificates : List (ControlFlow.Certificate ι) := []
  for (q, i) in r.codes.zipIdx do
    let hints := (codeHints[i]?).getD {}
    let C ← produceGraph (q.asRequest r) fuel labels suggestions known hints.sourceMap
      hints.requirements hints.cuts table
    certificates := certificates ++ [C]
    -- Search may use only definitions whose complete certificate checks,
    -- including their effect. Otherwise the defining expression must fail at
    -- its ordinary source obligation, rather than borrowing an unchecked code
    -- entry and failing only at the final generic certificate check.
    -- Retain every certificate: verifyJson still checks the entire code list.
    if GraphCode.codeCheckedUsing (graph r) (StoreView.images r.types) table q.entry C then
      table := table ++ [q.entry]
  let C ← produceGraph r fuel labels suggestions known sourceMap requirements cuts table
  let response := toJson (Response.mk C certificates)
  verifyJson σ request response
  return response

theorem verify_safe {r : Request σ ι} {c : Response ι} (hc : verify r c = true) (n W h ρ)
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
theorem verify_safe_at {r : Request σ ι} {c : Response ι} (hc : verify r c = true)
    (η : MixedAssignment ι) (n W h ρ)
    (he : EnvOk (reassign (graph r) η) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph r.program (meaning (reassign (graph r) η) r.result) n W h (.at r.start ρ) := by
  simp only [verify, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i table ht
    have hsound : ProgramCertificates.CodesSound (reassign (graph r) η) (GraphCode.admits table) := by
      unfold codeTable at ht
      split at ht
      · exact fun e he η' => GraphCode.checkCodes_sound ht e he η'
      · contradiction
    exact Parametricity.accepted_at hx η n W h ρ he hw hh hsound
  · contradiction

/-- Empty input contracts retain the closed-invocation corollary. -/
theorem verify_closed_safe {r : Request σ ι} {c : Response ι}
    (hc : verify r c = true) (hi : r.inputs = []) (n : Nat) :
    SafeGraph r.program (meaning (graph r) r.result) n (ofList []) []
      (.at r.start (fun _ => .nul)) := by
  apply verify_safe hc n _ [] _ _ WorldAdm_nil (emptyHeapOk n)
  rw [hi]
  exact ⟨fun _ => trivial, by simp⟩

theorem verify_claims {r : Request σ ι} {c : Response ι} (hc : verify r c = true) :
    c.certificate.map signature = r.claims := by
  simp only [verify, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · exact accept_claims hx
  · contradiction

/-- The JSON entry point certifies its decoded request at every budget, while
retaining exact claim identity. Source meaning is a separate extraction obligation. -/
theorem verifyJson_safe {request evidence : Json}
    (h : verifyJson (ι := ι) σ request evidence = .ok ()) :
    ∃ r c, decodeRequest σ request = .ok r ∧ decodeResponse r evidence = .ok c ∧
      c.certificate.map signature = r.claims ∧
      ∀ n W h ρ, EnvOk (graph r) r.inputs ρ n W → WorldAdm W → HeapOk n W h →
        SafeGraph r.program (meaning (graph r) r.result) n W h (.at r.start ρ) := by
  obtain ⟨r,c,hr,hc,hv⟩ := verifyJson_checked h
  exact ⟨r,c,hr,hc,verify_claims hv,verify_safe hv⟩

end

#print axioms verifyJson_safe
#print axioms verifyJson_checked
#print axioms verify_closed_safe
#print axioms verify_safe
#print axioms verify_safe_at
#print axioms verify_claims
end Verification.Model.RequestJson
