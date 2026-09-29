import Verification.Model.Types.Claim
import Verification.Model.Source.RequestJson

/-! Source types and the graph they are checked against. A program's types
are labels of a store (`LabelStore.Store`): extraction interns each compound
type the program mentions, so a label exists only because something used it,
and a clause the store lacks has no label rather than a wrong one. Primitive
unions translate exactly into the four primitive labels. The finite table of
clause rows in label order, which starts with the four primitive values, is
the store the pipeline runs on (`RequestJson.Table`). -/
namespace Verification.Model.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules LabelStore
open RequestJson (Row)

/-- A table of rows in label order: clause rows, and the scheme and parameter
rows generic methods need. -/
abbrev Table := RequestJson.Table

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

/-- Labels 0 to 3: null, true, false, undefined. -/
def initial : Table := [.clauses [.nul], .clauses [.boolLit true], .clauses [.boolLit false],
  .clauses [.undef]]

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

/-- Keep the store as it was when a translation fails, so a rejected candidate
leaves no rows behind. -/
def attempt (m : Lowering σ α) : Lowering σ (Except String α) := fun T =>
  match m.run T with
  | .ok (a, T') => .ok (.ok a, T')
  | .error e => .ok (.error e, T)

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

/-! ### The finite table

What the finite table's labels mean, row by row: a label interned for a
clause means exactly that clause, and the four primitive labels the four
primitive values. -/

/-- A finite table's intersections, for the SKJS export's tables: the
normalized conjunction of clause rows (`meetMany`), interned; an empty one is
refused, and so is an operand that is no clause row, which only the source
path's equations state (`EquationLowering.meetOf`). -/
instance : Meets Table Nat where
  meet parts := fun T => do
    let G := graph T
    if parts.any (fun A => A.isEmpty || !G.plainTy A) then
      throw "an intersection in a finite table is of clause rows"
    let cs := meetMany (parts.map (clausesOf G))
    if cs.isEmpty then throw "the intersection is empty: its operands have no value in common"
    let (T, l) := RequestJson.Table.intern T cs
    return ([l], T)

/-- A missing clause gets the table length, never a different contract. -/
def label (T : Table) (c : Clause (List Nat)) : Nat := T.idxOf (GraphRow.clauses [c])

/-- Give a clause a row if it lacks one. Appending keeps every existing label. -/
def intern (T : Table) (c : Clause (List Nat)) : Table := (RequestJson.Table.intern T [c]).1

theorem use_run (c : Clause (List Nat)) (T : Table) :
    (use c).run T = .ok (label (intern T c) c, intern T c) := rfl

theorem attempt_run (m : Lowering Table α) (T : Table) :
    (attempt m).run T = .ok (match m.run T with
      | .ok (a, T') => (.ok a, T') | .error e => (.error e, T)) := by
  unfold attempt StateT.run
  split <;> simp_all

theorem mem_intern (T : Table) (c : Clause (List Nat)) : GraphRow.clauses [c] ∈ intern T c := by
  unfold intern RequestJson.Table.intern
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem intern_prefix (T : Table) (c : Clause (List Nat)) : T <+: intern T c := by
  unfold intern RequestJson.Table.intern
  split
  · exact List.prefix_rfl
  · exact List.prefix_append _ _

theorem mem_of_prefix {T T' : Table} {d : Clause (List Nat)} (h : T <+: T') (hd : GraphRow.clauses [d] ∈ T) :
    GraphRow.clauses [d] ∈ T' := h.subset hd

/-- Labels already in use keep their index in every later table. -/
theorem label_of_prefix {T T' : Table} {d : Clause (List Nat)} (h : T <+: T') (hd : GraphRow.clauses [d] ∈ T) :
    label T' d = label T d := by
  obtain ⟨l, rfl⟩ := h
  simp [label, List.idxOf_append, hd]

theorem use_spec {c : Clause (List Nat)} {T T' : Table} {l : Nat}
    (h : (use c).run T = .ok (l, T')) : GraphRow.clauses [c] ∈ T' ∧ l = label T' c ∧ T <+: T' := by
  rw [use_run] at h
  cases h
  exact ⟨mem_intern T c, rfl, intern_prefix T c⟩

theorem label_exact {T : Table} {c : Clause (List Nat)} (hc : GraphRow.clauses [c] ∈ T) :
    expand (graph T) [label T c] = [c] := by
  have hi := List.idxOf_lt_length_iff.mpr hc
  have hx := List.getElem?_eq_some_iff.mpr ⟨hi,List.getElem_idxOf hi⟩
  have hp := RequestJson.tableGraph_clauses_row hx
  simp [expand, clausesOf, graph, label, NormalGraph.plainTy, hp.1, hp.2]

/-- A labelled clause means exactly that clause, read over the same table. -/
theorem label_meaning {T : Table} {c : Clause (List Nat)} (hc : GraphRow.clauses [c] ∈ T) (n W v) :
    meaning (graph T) [label T c] n W v ↔ clauseSem (graph T) c n W v := by
  have hp : (graph T).plainTy [label T c] = true := by
    have h := label_exact hc
    exact plain_of_mem_expand (c := c) (by simp [h])
  rw [expand_sem _ _ hp, label_exact hc]
  simp [semList, Tower.setSem]

theorem graph_initial {T : Table} (h : initial <+: T) {i : Nat} (hi : i < initial.length) :
    graph T i = initial[i].union := by
  obtain ⟨l, rfl⟩ := h
  have hx : (initial ++ l)[i]? = some initial[i] := by
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  have hr : ∀ j (hj : j < initial.length), ∃ cs, initial[j] = .clauses cs := by
    intro j hj
    match j, hj with
    | 0, _ => exact ⟨_, rfl⟩ | 1, _ => exact ⟨_, rfl⟩
    | 2, _ => exact ⟨_, rfl⟩ | 3, _ => exact ⟨_, rfl⟩
  obtain ⟨cs, hcs⟩ := hr i hi
  rw [hcs] at hx ⊢
  exact (RequestJson.tableGraph_clauses_row hx).2

theorem initial_plain {T : Table} (h : initial <+: T) {i : Nat} (hi : i < initial.length) :
    (graph T).plain i = true := by
  have hc := graph_initial h hi
  match i, hi with
  | 0, _ => exact NormalGraph.plain_of_clauses (c := .nul) (by rw [hc]; simp [initial, GraphRow.union])
  | 1, _ => exact NormalGraph.plain_of_clauses (c := .boolLit true) (by rw [hc]; simp [initial, GraphRow.union])
  | 2, _ => exact NormalGraph.plain_of_clauses (c := .boolLit false) (by rw [hc]; simp [initial, GraphRow.union])
  | 3, _ => exact NormalGraph.plain_of_clauses (c := .undef) (by rw [hc]; simp [initial, GraphRow.union])

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

/-- Numbers are interned rather than given fixed rows, because the singletons
are unbounded: the first four labels stay exactly the four primitive values,
so every existing label and every proof about them is untouched. -/
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

/-- One arm of a union, translated where the table can grow: its numbers are
interned and its fixed primitives translate exactly as before. `translate` is
the pure path and names only the four fixed labels, which is what a table that
cannot grow needs; wherever one can grow, a number belongs in it. -/
def translateArm (t : Claim.Ty) : Lowering σ (Ty ι) := do
  -- `unknown` is semantic top: every value, and no operation through it.
  if t.top then return [← use .top]
  let numbers ← numberLabels ⟨t.top, t.atoms.filter isNumberAtom⟩
  let others ← match translate ⟨t.top, t.atoms.filter (fun a => !isNumberAtom a)⟩ with
    | .ok A => pure A
    | .error e => throw e
  return (numbers ++ others).mergeSort Labels.le |>.eraseDups

end

/-- This characterization also rules out extra nonprimitive modeled values. -/
theorem encode_meaning {T : Table} (h : initial <+: T) (t : Claim.Ty) (n W v) :
    meaning (graph T) (encode t) n W v ↔
      (admits t .vnull = true ∧ v = .nul) ∨
      (admits t (.vbool true) = true ∧ v = .tru) ∨
      (admits t (.vbool false) = true ∧ v = .fls) ∨
      (admits t .vundef = true ∧ v = .undef) := by
  have h0 : graph T 0 = [.nul] := graph_initial h (by decide)
  have h1 : graph T 1 = [.boolLit true] := graph_initial h (by decide)
  have h2 : graph T 2 = [.boolLit false] := graph_initial h (by decide)
  have h3 : graph T 3 = [.undef] := graph_initial h (by decide)
  have hp : (graph T).plainTy (encode t) = true := by
    simp only [NormalGraph.plainTy, List.all_eq_true]
    intro i hi
    have : i < initial.length := by
      simp only [encode, List.mem_append] at hi
      simp [initial]
      rcases hi with ((hi | hi) | hi) | hi <;> split at hi <;> simp_all
    exact initial_plain h this
  rw [expand_sem _ _ hp, expand_of_plain hp]
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;> cases hu : admits t .vundef <;>
    simp [encode, hn, ht, hf, hu, clausesOf, h0, h1, h2, h3, Tower.setSem, rowSem,
      realmInvariant_iff_of_not_record (show (Clause.nul : Clause (List Nat)).record = false from rfl),
      realmInvariant_iff_of_not_record (show (Clause.undef : Clause (List Nat)).record = false from rfl),
      realmInvariant_iff_of_not_record (show (Clause.boolLit true : Clause (List Nat)).record = false from rfl),
      realmInvariant_iff_of_not_record (show (Clause.boolLit false : Clause (List Nat)).record = false from rfl),
      semWithArgs, nulT, undefT]

/-- No atom of the primitive fragment admits a number, so a numeric value is
outside every type that fragment can state. `value` decodes one because the
number labels are interned elsewhere; this keeps the pure path exact. -/
theorem supported_not_num {a : Claim.Atom} (h : supportedAtom a = true) (b : UInt64) :
    Claim.inhabits (.vnum b) a = false := by
  cases a <;> simp_all [supportedAtom, Claim.inhabits]

/-- Likewise no atom of the primitive fragment admits a string. -/
theorem supported_not_str {a : Claim.Atom} (h : supportedAtom a = true) (s : String) :
    Claim.inhabits (.vstr s) a = false := by
  cases a <;> simp_all [supportedAtom, Claim.inhabits]

/-- Likewise no atom of the primitive fragment admits a bigint. -/
theorem supported_not_bigint {a : Claim.Atom} (h : supportedAtom a = true) (i : Int) :
    Claim.inhabits (.vbigint i) a = false := by
  cases a <;> simp_all [supportedAtom, Claim.inhabits]

/-- Supported claim-value membership is preserved in both directions. -/
theorem translate_exact {T : Table} (hT : initial <+: T) {t : Claim.Ty} {A u v}
    (ht : translate t = .ok A) (hv : value u = .ok v) (n W) :
    Claim.mem u t ↔ meaning (graph T) A n W v := by
  unfold translate at ht
  split at ht
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have htop : t.top = false := by simpa using h.1
    cases ht
    rw [encode_meaning hT]
    cases u <;> simp only [value] at hv
    all_goals try contradiction
    · cases hv
      simp [Claim.mem, htop, admits, List.any_eq_true]
    · cases hv
      simp [Claim.mem, htop, admits, List.any_eq_true]
    · -- A number: neither side holds, for the same reason.
      rename_i b
      cases hv
      have hall := List.all_eq_true.mp h.2
      have hno : ∀ a ∈ t.atoms, Claim.inhabits (.vnum b) a = false :=
        fun a ha => supported_not_num (hall a ha) b
      simp only [Claim.mem, htop, admits, List.any_eq_true, Bool.false_eq_true,
        false_or, encode, not_exists]
      simpa using hno
    · -- A string: neither side holds, for the same reason.
      rename_i s
      cases hv
      have hall := List.all_eq_true.mp h.2
      have hno : ∀ a ∈ t.atoms, Claim.inhabits (.vstr s) a = false :=
        fun a ha => supported_not_str (hall a ha) s
      simp only [Claim.mem, htop, admits, List.any_eq_true, Bool.false_eq_true,
        false_or, encode, not_exists]
      simpa using hno
    · rename_i b
      cases b <;> cases hv <;> simp [Claim.mem, htop, admits, List.any_eq_true]
    · -- A bigint: neither side holds, for the same reason.
      rename_i i
      cases hv
      have hall := List.all_eq_true.mp h.2
      have hno : ∀ a ∈ t.atoms, Claim.inhabits (.vbigint i) a = false :=
        fun a ha => supported_not_bigint (hall a ha) i
      simp only [Claim.mem, htop, admits, List.any_eq_true, Bool.false_eq_true,
        false_or, encode, not_exists]
      simpa using hno
  · contradiction

/-- Exact arrow interpretation, including its contravariant receiver and
domain, over any table holding the row: the one-domain call contract, whatever
code meets it. -/
theorem arrow_exact {T : Table} {Rc D R : Ty Nat} {effect : CallEffects.Effect}
    (hm : GraphRow.clauses [.arrs [⟨Rc,[D],R,effect⟩] []] ∈ T) (n W v) :
    meaning (graph T) [label T (.arrs [⟨Rc,[D],R,effect⟩] [])] n W v ↔
      CallEffects.callsT [⟨meaning (graph T) Rc, [meaning (graph T) D], meaning (graph T) R,effect⟩] n W v := by
  rw [label_meaning hm]
  simp only [clauseSem, rowSem, PositiveNormalization.semWithArgs, List.map_cons, List.map_nil]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, h.1, by simp⟩, realmInvariant_of_not_record rfl _ _ _⟩⟩

#print axioms arrow_exact
#print axioms translate_exact
#print axioms label_meaning
end Verification.Model.SourceTypes
