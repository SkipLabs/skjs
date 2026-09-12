import Verification.ExperimentState.SourceEncoding
import Verification.ExperimentState.RequestJson

/-! Source types and the graph they are checked against. A program's graph is a
table of clause rows in label order. It starts with the four primitive values
and grows by interning each compound type the program mentions, so a label
exists only because something used it, and a clause the table lacks has no
label rather than a wrong one. Primitive unions translate exactly into the
fixed first four labels. -/
namespace Verification.ExperimentState.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

abbrev Table := List (List (Clause (List Nat)))

/-- Labels 0 to 3: null, true, false, undefined. -/
def initial : Table := [[.nul],[.boolLit true],[.boolLit false],[.undef]]

def isPrimitive (i : Nat) : Bool := i < initial.length

def graph (T : Table) : NormalGraph Nat := fun i => T[i]?.getD []

/-- A missing clause gets the table length, never a different contract. -/
def label (T : Table) (c : Clause (List Nat)) : Nat := T.idxOf [c]

/-- Give a clause a row if it lacks one. Appending keeps every existing label. -/
def intern (T : Table) (c : Clause (List Nat)) : Table :=
  if [c] ∈ T then T else T ++ [[c]]

/-- Translation grows the table as it goes. -/
abbrev Lowering := StateT Table (Except String)

def use (c : Clause (List Nat)) : Lowering Nat :=
  modifyGet fun T => let T' := intern T c; (label T' c, T')

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

def admits (t : Wire.Ty) (v : Wire.Val) : Bool := t.atoms.any (Wire.inhabits v)

def encode (t : Wire.Ty) : Ty Nat :=
  (if admits t .vnull then [0] else []) ++
  (if admits t (.vbool true) then [1] else []) ++
  (if admits t (.vbool false) then [2] else []) ++
  (if admits t .vundef then [3] else [])

def supportedAtom : Wire.Atom → Bool
  | .null | .undef | .bool | .boolLit _ => true
  | _ => false

def translate (t : Wire.Ty) : Except String (Ty Nat) :=
  if !t.top && t.atoms.all supportedAtom then .ok (encode t)
  else .error "source type outside the null/undefined/boolean/singleton source slice"

def value : Wire.Val → Except String Tm
  | .vnull => .ok .nul
  | .vundef => .ok .undef
  | .vbool true => .ok .tru
  | .vbool false => .ok .fls
  | _ => .error "source literal outside the null/undefined/boolean source slice"

/-- This characterization also rules out extra nonprimitive modeled values. -/
theorem encode_meaning {T : Table} (h : initial <+: T) (t : Wire.Ty) (n W v) :
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

/-- Supported wire-value membership is preserved in both directions. -/
theorem translate_exact {T : Table} (hT : initial <+: T) {t : Wire.Ty} {A u v}
    (ht : translate t = .ok A) (hv : value u = .ok v) (n W) :
    Wire.mem u t ↔ meaning (graph T) A n W v := by
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
      simp [Wire.mem, htop, admits, List.any_eq_true]
    · cases hv
      simp [Wire.mem, htop, admits, List.any_eq_true]
    · rename_i b
      cases b <;> cases hv <;> simp [Wire.mem, htop, admits, List.any_eq_true]
  · contradiction

/-- Exact arrow interpretation, including its contravariant domain, over any
table holding the row. -/
theorem arrow_exact {T : Table} {D R : Ty Nat} (hm : [.arrs [(D,R)]] ∈ T) (n W v) :
    meaning (graph T) [label T (.arrs [(D,R)])] n W v ↔
      arrowT (meaning (graph T) D) (meaning (graph T) R) n W v := by
  rw [label_meaning hm]
  simpa [PositiveNormalization.sem] using
    arrowsT_singleton (meaning (graph T) D) (meaning (graph T) R) n W v

#print axioms arrow_exact
#print axioms translate_exact
#print axioms label_meaning
end Verification.ExperimentState.SourceTypes
