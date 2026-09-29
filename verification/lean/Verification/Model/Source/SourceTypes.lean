import Verification.Model.Types.Claim
import Verification.Model.Source.RequestJson

/-! Source types and the graph they are checked against. A program's types
are labels of a store (`LabelStore.Store`): extraction interns each compound
type the program mentions, so a label exists only because something used it,
and a clause the store lacks has no label rather than a wrong one. Primitive
unions translate into the four primitive labels. -/
namespace Verification.Model.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules LabelStore

/-- The field an array object holds its store in. No source name spells it. -/
def storeField : PropKey := CallArguments.arrayStoreField

/-- The field an object holds its prototype in. No source name spells it. -/
def protoField : PropKey := CallArguments.protoField

/-- A name in double brackets, which the model keeps for itself
(`RequestJson.bracketed`). -/
abbrev bracketed : PropKey → Bool := RequestJson.bracketed

/-- A key the model keeps for itself: the array store, the prototype, and
every other name in double brackets (`RequestJson.reservedKey`). -/
abbrev reservedKey : PropKey → Bool := RequestJson.reservedKey

/-- The module value holding `Array.prototype`: a name no source identifier
spells, at `ArrayProto`. Every array a unit allocates takes its prototype from
it, as JavaScript takes the realm's. -/
def arrayPrototypeName : String := "[[Array.prototype]]"

/-- The module values holding the primitive wrappers' prototypes, each at its
contract (`StringProto`, `NumberProto`, `BigIntProto`, `BooleanProto`), named
as `[[Array.prototype]]` is: a member of a primitive of the tag's shape is read
from it, as JavaScript's `ToObject` reads it from the realm's. -/
def primitivePrototypes : List (Tag × String) :=
  [(.isStr, "[[String.prototype]]"), (.isNum, "[[Number.prototype]]"),
   (.isBigint, "[[BigInt.prototype]]"), (.isBool, "[[Boolean.prototype]]")]

/-- Every realm prototype a unit may read through, whether or not it names it. -/
def prototypeNames : List String := arrayPrototypeName :: primitivePrototypes.map (·.2)

/-- An array type: its store at `store`, invariant or, for a readonly array, a
view; the prototype as a view at `proto`, `ArrayProto`; and none of `excluded`,
the keys `ArrayProto` provides plus `constructor` (`arrayExcludedKeys`), among
its own keys, so a read of one of them continues at the prototype. -/
def arrayClause (excluded : List PropKey) (store proto : ι) (readonly : Bool) : Clause (List ι) :=
  PositiveNormalization.arrayClauseOf [store] [proto] excluded readonly

/-- The keys an array cannot own: `constructor` and those `ArrayProto`'s row
(`proto`) names, its fields, views, optional fields and methods, the reserved
keys aside. An array owns none of them, so reading one continues at the
prototype; any other own key an array may have. -/
def arrayExcludedKeys (G : NormalGraph ι) (proto : ι) : List PropKey :=
  RequestJson.arrayExcludedKeysOf (expand G [proto])
where
  /-- Canonical excluded array keys (`RequestJson.arrayExcludedKeys`). -/
  ofKeys (ks : List PropKey) : List PropKey := RequestJson.arrayExcludedKeys ks

/-- No reserved key is a prototype key: every array owns its store and its
prototype. -/
theorem arrayExcludedKeys_ofKeys_reserved {ks : List PropKey} {k : PropKey}
    (h : k ∈ arrayExcludedKeys.ofKeys ks) : reservedKey k = false := by
  have := List.mem_filter.mp ((List.mem_eraseDups).mp ((List.mem_mergeSort).mp h))
  simpa using this.2

theorem arrayExcludedKeys_reserved {G : NormalGraph ι} {proto : ι} {k : PropKey}
    (h : k ∈ arrayExcludedKeys G proto) : reservedKey k = false := by
  unfold arrayExcludedKeys RequestJson.arrayExcludedKeysOf at h
  split at h <;> exact arrayExcludedKeys_ofKeys_reserved h

section
variable {σ ι : Type} [Labels ι] [Store σ ι]

def graph (T : σ) : NormalGraph ι := StoreView.graph T

/-- The array type over `store` in the store's own graph. -/
def arrayOf (T : σ) (store : ι) (readonly : Bool) : Clause (List ι) :=
  arrayClause (arrayExcludedKeys (graph T) (StoreView.arrayProto T)) store (StoreView.arrayProto T) readonly

/-- The one user-facing rendering boundary for graph types. Labels are
implementation references into the store, so diagnostics must call this
function rather than interpolate a `Ty ι`. The fallback names the semantic
kind and never exposes a label. -/
private def clauseName : Clause (List ι) → String
  | .nul => "null"
  | .bool => "boolean"
  | .refs .. => "object"
  | .dict .. => "indexed object"
  | .arrs .. => "function"
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .num => "number"
  | .numLit _ => "numeric literal"
  | .undef => "undefined"
  | .callable .. => "callable object"
  | .top => "unknown"
  | .str => "string"
  | .strLit _ => "string literal"
  | .list .. => "array"
  | .pack .. => "argument list"
  | .bigint => "bigint"
  | .bigintLit _ => "bigint literal"
  | .symbol => "symbol"
  | .ctors .. => "constructor"

def render (T : σ) (A : Ty ι) : String :=
  match expand (graph T) A with
  | [] => "never"
  | [.boolLit true, .boolLit false] | [.boolLit false, .boolLit true] => "boolean"
  | cs => String.intercalate " | " (cs.map clauseName).eraseDups

/-- Translation grows the store as it goes. -/
abbrev Lowering (σ : Type) := StateT σ (Except String)

/-- A union of clauses' label, interning it if the store lacks it. It
remains a union of its clauses; this does not make it an intersection or
assert a producer equation. -/
def useRow (row : List (Clause (List ι))) : Lowering σ ι :=
  modifyGet fun T => let (T, l) := Store.intern T row; (l, T)

def use (c : Clause (List ι)) : Lowering σ ι := useRow [c]

/-- The parameter that stands for a generic unit's binder `name`
(`Store.binder`). -/
def binderRow (name : String) : Lowering σ ι := fun T => do
  let (T, l) ← Store.binder T name
  return (l, T)

/-- What a binder's parameter is met with when its bound is another binder,
read as `r`: the parameter `r`, within `r`'s clauses and parameters when `r`
is itself a meet. `U extends T` is `U ⊓ T`, which is below `T`
(`PositiveRules.meetBelow`): at every instantiation within the bound, the
meet is the binder. -/
def dependentMeet (T : σ) (r : ι) : Option (List (Clause (List ι)) × List ι) :=
  match StoreView.row T r with
  | .param _ _ .value => some ([.top], [r])
  | .meet q cs ps => some (cs, q :: ps)
  | _ => none

/-- A bounded binder's label: the parameter `p` within `cs` and the
parameters `also` (`Store.bounded`). -/
def bounded (p : ι) (cs : List (Clause (List ι))) (also : List ι := []) : Lowering σ ι :=
  modifyGet fun T => let (T, l) := Store.bounded T p cs also; (l, T)

/-- A type with each label replaced by the first label of the same row. Rows
with identical clauses denote the same type: a declaration's row and an
annotation's row can coincide without being the same label, for instance when
a producer interned the annotation before the declaration row was filled. -/
def canonical (T : σ) (A : List ι) : List ι :=
  (A.map fun label => if StoreView.valid T label then
      ((StoreView.labels T).find? (fun m => StoreView.row T m == StoreView.row T label)).getD label
    else label)
    |>.eraseDups.mergeSort Labels.le

end

/-- A source annotation in claim form with the named binders read as their
parameter rows: each binder atom becomes the graph atom of its row. -/
partial def annotationAtRows [Lean.ToJson ι] (rows : List (String × ι)) : Lean.Json → Lean.Json
  | .arr xs => .arr (xs.map (annotationAtRows rows))
  | .obj kvs =>
    let j := Lean.Json.obj kvs
    match (j.getObjValAs? String "a").toOption, (j.getObjValAs? String "name").toOption with
    | some "param", some name =>
      match rows.lookup name with
      | some l => if j == Lean.Json.mkObj [("a", Lean.toJson "param"), ("name", Lean.toJson name)] then
          Lean.Json.mkObj [("a", Lean.toJson "graph"), ("label", Lean.toJson l)] else j
      | none => j
    | _, _ => Lean.Json.mkObj (kvs.toList.map fun (k, v) => (k, annotationAtRows rows v))
  | j => j

/-- The binder names a claim-form annotation mentions. -/
partial def binderNames : Lean.Json → List String
  | .arr xs => (xs.toList.flatMap binderNames).eraseDups
  | .obj kvs =>
    let j := Lean.Json.obj kvs
    match (j.getObjValAs? String "a").toOption, (j.getObjValAs? String "name").toOption with
    | some "param", some name => [name]
    | _, _ => (kvs.toList.flatMap fun (_, v) => binderNames v).eraseDups
  | _ => []

def admits (t : Claim.Ty) (v : Claim.Val) : Bool := t.atoms.any (Claim.inhabits v)

section
variable {σ ι : Type} [Labels ι] [Store σ ι]

def encode (t : Claim.Ty) : Ty ι :=
  (if admits t .vnull then [Labels.nul] else []) ++
  (if admits t (.vbool true) then [Labels.tru] else []) ++
  (if admits t (.vbool false) then [Labels.fls] else []) ++
  (if admits t .vundef then [Labels.undef] else [])

def supportedAtom : Claim.Atom → Bool
  | .null | .undef | .bool | .boolLit _ => true
  | _ => false

def translate (t : Claim.Ty) : Except String (Ty ι) :=
  if !t.top && t.atoms.all supportedAtom then .ok (encode t)
  else .error "source type outside the null/undefined/boolean/singleton fragment"

def value : Claim.Val → Except String Tm
  | .vnull => .ok .nul
  | .vundef => .ok .undef
  | .vbool true => .ok .tru
  | .vbool false => .ok .fls
  | .vnum b => .ok (.num b)
  | .vstr s => .ok (.str s)
  | .vbigint i => .ok (.bigint i)

/-- Numbers, strings, bigints and symbols are interned rather than given fixed
labels, because their singletons are unbounded; the four fixed labels are the
primitive values. -/
def numberLabels (t : Claim.Ty) : Lowering σ (Ty ι) := do
  let mut out := []
  for a in t.atoms do
    match a with
    | .num => out := out ++ [← use .num]
    | .numLit b =>
      -- TypeScript's literal type 0 includes both runtime zeros. The graph's
      -- bit singletons remain exact, so state both rather than erase a sign.
      out := out ++ [← use (.numLit b)]
      if Float.ofBits b == 0.0 then
        out := out ++ [← use (.numLit (9223372036854775808 : UInt64))]
    | .str => out := out ++ [← use .str]
    | .strLit s => out := out ++ [← use (.strLit s)]
    | .bigint => out := out ++ [← use .bigint]
    | .bigintLit i => out := out ++ [← use (.bigintLit i)]
    | .symbol => out := out ++ [← use .symbol]
    -- A void result forgets its guarantee: every value, like `unknown`.
    | .void => out := out ++ [← use .top]
    | _ => pure ()
  return out

/-- Numbers and strings are interned, as their singletons are unbounded. -/
def isNumberAtom : Claim.Atom → Bool
  | .num | .numLit _ | .str | .strLit _ | .void | .bigint | .bigintLit _ | .symbol => true
  | _ => false

/-- One arm of a union: its numbers and strings interned, its fixed
primitives translated to the four fixed labels (`translate`). -/
def translateArm (t : Claim.Ty) : Lowering σ (Ty ι) := do
  -- `unknown` is semantic top: every value, and no operation through it.
  if t.top then return [← use .top]
  let numbers ← numberLabels ⟨t.top, t.atoms.filter isNumberAtom⟩
  let others ← match translate ⟨t.top, t.atoms.filter (fun a => !isNumberAtom a)⟩ with
    | .ok A => pure A
    | .error e => throw e
  return (numbers ++ others).mergeSort Labels.le |>.eraseDups

end

end Verification.Model.SourceTypes
