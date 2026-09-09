import Verification.ExperimentState.SourceEncoding
import Verification.ExperimentState.RequestJson

/-! Exact translation of the supported source/claim type encoding. The shared
input decoder represents primitive unions as Wire.Ty; this module interprets
that current wire format in the stateful calculus, not an earlier evaluator. -/
namespace Verification.ExperimentState.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

-- Canonical subsets, indexed by null/true/false bits. Keep null-argument
-- arrows first, so existing cell and null-arrow labels retain their meaning.
def primitiveTypes : List (Ty Nat) :=
  [[],[0],[1],[0,1],[2],[0,2],[1,2],[0,1,2]]

def argumentTypes : List (Ty Nat) :=
  [[0],[],[1],[0,1],[2],[0,2],[1,2],[0,1,2]]

def baseTypes : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false]] ++
  primitiveTypes.map (fun A => [.refs A []]) ++
  argumentTypes.flatMap (fun D => primitiveTypes.map (fun R => [.arrs [(D,R)]]))
/-- Keep every existing label stable. Undefined is label 75; append all missing
reference and unary-arrow combinations over the four primitive values. -/
def allPrimitiveTypes : List (Ty Nat) :=
  primitiveTypes ++ primitiveTypes.map (· ++ [75])
def allArgumentTypes : List (Ty Nat) :=
  argumentTypes ++ primitiveTypes.map (· ++ [75])
def compoundTypes : List (List (Clause (List Nat))) :=
  allPrimitiveTypes.map (fun A => [.refs A []]) ++
  allArgumentTypes.flatMap (fun D => allPrimitiveTypes.map (fun R => [.arrs [(D,R)]])) ++
  -- Appended last, so every label already in use keeps its index. A location
  -- under two invariant contracts at once; both orders are generated, since
  -- they denote the same conjunction but are different clauses to a lookup, and
  -- having both spares every caller a canonical ordering.
  allPrimitiveTypes.flatMap (fun A => allPrimitiveTypes.map (fun B => [.refs A [B]]))
def types : List (List (Clause (List Nat))) :=
  baseTypes ++ [[.undef]] ++ compoundTypes.filter (fun c => !baseTypes.contains c)
#guard types.length == 532

def isPrimitive (i : Nat) : Bool := i < 3 || i == 75

/-- A missing clause gets an out-of-range label, never a different contract. -/
def label (c : Clause (Ty Nat)) : Nat := types.idxOf [c]

theorem compound_mem {c} (hc : [c] ∈ compoundTypes) : [c] ∈ types := by
  by_cases hb : [c] ∈ baseTypes
  · exact List.mem_append_left _ (List.mem_append_left _ hb)
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hc,by simpa using hb⟩)


def graph : NormalGraph Nat := fun i => types[i]?.getD []

@[simp] theorem graph_nul : graph 0 = [.nul] := rfl
@[simp] theorem graph_tru : graph 1 = [.boolLit true] := rfl
@[simp] theorem graph_fls : graph 2 = [.boolLit false] := rfl
@[simp] theorem graph_undef : graph 75 = [.undef] := rfl

theorem label_exact {c} (hc : [c] ∈ types) : expand graph [label c] = [c] := by
  have hi := List.idxOf_lt_length_iff.mpr hc
  have hx := List.getElem?_eq_some_iff.mpr ⟨hi,List.getElem_idxOf hi⟩
  simp [expand,graph,label,hx]

def admits (t : Wire.Ty) (v : Wire.Val) : Bool := t.atoms.any (Wire.inhabits v)

def encode (t : Wire.Ty) : Ty Nat :=
  (if admits t .vnull then [0] else []) ++
  (if admits t (.vbool true) then [1] else []) ++
  (if admits t (.vbool false) then [2] else []) ++
  (if admits t .vundef then [75] else [])

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

theorem encode_mem (t : Wire.Ty) : encode t ∈ allPrimitiveTypes := by
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;> cases hu : admits t .vundef <;>
    simp [encode,hn,ht,hf,hu,allPrimitiveTypes,primitiveTypes]

theorem encode_argument_mem (t : Wire.Ty) : encode t ∈ allArgumentTypes := by
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;> cases hu : admits t .vundef <;>
    simp [encode,hn,ht,hf,hu,allArgumentTypes,argumentTypes,primitiveTypes]

/-- This characterization also rules out extra nonprimitive modeled values. -/
theorem encode_meaning (t : Wire.Ty) (n W v) :
    meaning graph (encode t) n W v ↔
      (admits t .vnull = true ∧ v = .nul) ∨
      (admits t (.vbool true) = true ∧ v = .tru) ∨
      (admits t (.vbool false) = true ∧ v = .fls) ∨
      (admits t .vundef = true ∧ v = .undef) := by
  rw [expand_sem]
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;> cases hu : admits t .vundef <;>
    simp [encode, hn, ht, hf, hu, expand, semList, Tower.setSem, sem, nulT, undefT]

/-- Supported wire-value membership is preserved in both directions. -/
theorem translate_exact {t : Wire.Ty} {A u v}
    (ht : translate t = .ok A) (hv : value u = .ok v) (n W) :
    Wire.mem u t ↔ meaning graph A n W v := by
  unfold translate at ht
  split at ht
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have htop : t.top = false := by simpa using h.1
    cases ht
    rw [encode_meaning]
    cases u <;> simp only [value] at hv
    all_goals try contradiction
    · cases hv
      simp [Wire.mem, htop, admits, List.any_eq_true]
    · cases hv
      simp [Wire.mem, htop, admits, List.any_eq_true]
    · rename_i b
      cases b <;> cases hv <;> simp [Wire.mem, htop, admits, List.any_eq_true]
  · contradiction

#print axioms translate_exact
end Verification.ExperimentState.SourceTypes
