import Verification.Model.Types.Claim
import Verification.Model.Source.RequestJson

/-! Source types and the graph they are checked against. A program's graph is a
table of clause rows in label order. It starts with the four primitive values
and grows by interning each compound type the program mentions, so a label
exists only because something used it, and a clause the table lacks has no
label rather than a wrong one. Primitive unions translate exactly into the
fixed first four labels. -/
namespace Verification.Model.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

abbrev Table := List (List (Clause (List Nat)))

/-- The field an array object holds its store in. No source name spells it. -/
def storeField : PropKey := "[]"

/-- Labels 0 to 3: null, true, false, undefined. -/
def initial : Table := [[.nul],[.boolLit true],[.boolLit false],[.undef]]

def isPrimitive (i : Nat) : Bool := i < initial.length

def graph (T : Table) : NormalGraph Nat := fun i => T[i]?.getD []

/-- The one user-facing rendering boundary for graph types. Label numbers are
implementation references into `Table`, so diagnostics must call this function
rather than interpolate a `Ty Nat`. The fallback names the semantic kind and
never exposes its row indices. -/
private def clauseName : Clause (List Nat) → String
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
  | .bigint => "bigint"
  | .symbol => "symbol"

def render (T : Table) (A : Ty Nat) : String :=
  match expand (graph T) A with
  | [] => "never"
  | [.boolLit true, .boolLit false] | [.boolLit false, .boolLit true] => "boolean"
  | cs => String.intercalate " | " (cs.map clauseName).eraseDups

#guard render initial [1, 2] == "boolean"

/-- A missing clause gets the table length, never a different contract. -/
def label (T : Table) (c : Clause (List Nat)) : Nat := T.idxOf [c]

/-- Give a clause a row if it lacks one. Appending keeps every existing label. -/
def intern (T : Table) (c : Clause (List Nat)) : Table :=
  if [c] ∈ T then T else T ++ [[c]]

/-- Translation grows the table as it goes. -/
abbrev Lowering := StateT Table (Except String)

def use (c : Clause (List Nat)) : Lowering Nat :=
  modifyGet fun T => let T' := intern T c; (label T' c, T')

/-- A type with each label replaced by the first row of the same content.
Rows with identical clauses denote the same type: a declaration's row and an
annotation's row can coincide without being the same label, for instance when
a producer interned the annotation before the declaration row was filled. -/
def canonical (T : Table) (A : List Nat) : List Nat :=
  (A.map fun label => (List.range T.length).find? (fun m => T[m]? == T[label]?) |>.getD label)
    |>.eraseDups.mergeSort (· ≤ ·)

/-- Intern a finite union as one graph row. It remains a union of its clauses;
this does not make it an intersection or assert a producer equation. -/
def useRow (row : List (Clause (List Nat))) : Lowering Nat :=
  modifyGet fun T =>
    let T' := if row ∈ T then T else T ++ [row]
    (T'.idxOf row, T')

/-- Keep the table as it was when a translation fails, so a rejected candidate
leaves no rows behind. -/
def attempt (m : Lowering α) : Lowering (Except String α) := fun T =>
  match m.run T with
  | .ok (a, T') => .ok (.ok a, T')
  | .error e => .ok (.error e, T)

theorem use_run (c : Clause (List Nat)) (T : Table) :
    (use c).run T = .ok (label (intern T c) c, intern T c) := rfl

theorem attempt_run (m : Lowering α) (T : Table) :
    (attempt m).run T = .ok (match m.run T with
      | .ok (a, T') => (.ok a, T') | .error e => (.error e, T)) := by
  unfold attempt StateT.run
  split <;> simp_all

theorem mem_intern (T : Table) (c : Clause (List Nat)) : [c] ∈ intern T c := by
  unfold intern
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem intern_prefix (T : Table) (c : Clause (List Nat)) : T <+: intern T c := by
  unfold intern
  split
  · exact List.prefix_rfl
  · exact List.prefix_append _ _

theorem mem_of_prefix {T T' : Table} {d : Clause (List Nat)} (h : T <+: T') (hd : [d] ∈ T) :
    [d] ∈ T' := h.subset hd

/-- Labels already in use keep their index in every later table. -/
theorem label_of_prefix {T T' : Table} {d : Clause (List Nat)} (h : T <+: T') (hd : [d] ∈ T) :
    label T' d = label T d := by
  obtain ⟨l, rfl⟩ := h
  simp [label, List.idxOf_append, hd]

theorem use_spec {c : Clause (List Nat)} {T T' : Table} {l : Nat}
    (h : (use c).run T = .ok (l, T')) : [c] ∈ T' ∧ l = label T' c ∧ T <+: T' := by
  rw [use_run] at h
  cases h
  exact ⟨mem_intern T c, rfl, intern_prefix T c⟩

theorem label_exact {T : Table} {c : Clause (List Nat)} (hc : [c] ∈ T) :
    expand (graph T) [label T c] = [c] := by
  have hi := List.idxOf_lt_length_iff.mpr hc
  have hx := List.getElem?_eq_some_iff.mpr ⟨hi,List.getElem_idxOf hi⟩
  simp [expand,graph,label,hx]

/-- A labelled clause means exactly that clause, read over the same table. -/
theorem label_meaning {T : Table} {c : Clause (List Nat)} (hc : [c] ∈ T) (n W v) :
    meaning (graph T) [label T c] n W v ↔ sem (meaning (graph T)) c n W v := by
  rw [expand_sem, label_exact hc]
  simp [semList, Tower.setSem]

theorem graph_initial {T : Table} (h : initial <+: T) {i : Nat} (hi : i < initial.length) :
    graph T i = initial[i] := by
  obtain ⟨l, rfl⟩ := h
  simp [graph, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

def admits (t : Claim.Ty) (v : Claim.Val) : Bool := t.atoms.any (Claim.inhabits v)

def encode (t : Claim.Ty) : Ty Nat :=
  (if admits t .vnull then [0] else []) ++
  (if admits t (.vbool true) then [1] else []) ++
  (if admits t (.vbool false) then [2] else []) ++
  (if admits t .vundef then [3] else [])

def supportedAtom : Claim.Atom → Bool
  | .null | .undef | .bool | .boolLit _ => true
  | _ => false

def translate (t : Claim.Ty) : Except String (Ty Nat) :=
  if !t.top && t.atoms.all supportedAtom then .ok (encode t)
  else .error "source type outside the null/undefined/boolean/singleton fragment"

def value : Claim.Val → Except String Tm
  | .vnull => .ok .nul
  | .vundef => .ok .undef
  | .vbool true => .ok .tru
  | .vbool false => .ok .fls
  | .vnum b => .ok (.num b)
  | .vstr s => .ok (.str s)

/-- Numbers are interned rather than given fixed rows, because the singletons
are unbounded: the first four labels stay exactly the four primitive values,
so every existing label and every proof about them is untouched. -/
def numberLabels (t : Claim.Ty) : Lowering (Ty Nat) := do
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
    | .symbol => out := out ++ [← use .symbol]
    -- A void result forgets its guarantee: every value, like `unknown`.
    | .void => out := out ++ [← use .top]
    | _ => pure ()
  return out

/-- Numbers and strings are interned, as their singletons are unbounded. -/
def isNumberAtom : Claim.Atom → Bool
  | .num | .numLit _ | .str | .strLit _ | .void | .bigint | .symbol => true
  | _ => false

/-- One arm of a union, translated where the table can grow: its numbers are
interned and its fixed primitives translate exactly as before. `translate` is
the pure path and names only the four fixed labels, which is what a table that
cannot grow needs; wherever one can grow, a number belongs in it. -/
def translateArm (t : Claim.Ty) : Lowering (Ty Nat) := do
  -- `unknown` is semantic top: every value, and no operation through it.
  if t.top then return [← use .top]
  let numbers ← numberLabels ⟨t.top, t.atoms.filter isNumberAtom⟩
  let others ← match translate ⟨t.top, t.atoms.filter (fun a => !isNumberAtom a)⟩ with
    | .ok A => pure A
    | .error e => throw e
  return (numbers ++ others).mergeSort (· ≤ ·) |>.eraseDups

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
  rw [expand_sem]
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;> cases hu : admits t .vundef <;>
    simp [encode, hn, ht, hf, hu, expand, h0, h1, h2, h3, semList, Tower.setSem, sem, nulT, undefT]

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
  · contradiction

/-- Exact arrow interpretation, including its contravariant receiver and
domain, over any table holding the row: the one-domain call contract, whatever
code meets it. -/
theorem arrow_exact {T : Table} {Rc D R : Ty Nat} (hm : [.arrs [(Rc,[D],R)] []] ∈ T) (n W v) :
    meaning (graph T) [label T (.arrs [(Rc,[D],R)] [])] n W v ↔
      callsT [(meaning (graph T) Rc, [meaning (graph T) D], meaning (graph T) R)] n W v := by
  rw [label_meaning hm]
  simp only [PositiveNormalization.sem, List.map_cons, List.map_nil]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1, by simp⟩⟩

#print axioms arrow_exact
#print axioms translate_exact
#print axioms label_meaning
end Verification.Model.SourceTypes
