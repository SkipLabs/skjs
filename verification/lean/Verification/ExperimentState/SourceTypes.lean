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

def types : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false]] ++
  primitiveTypes.map (fun A => [.refs A []]) ++
  argumentTypes.flatMap (fun D => primitiveTypes.map (fun R => [.arrs [(D,R)]]))
#guard types.length == 75

def graph : NormalGraph Nat := fun i => types[i]?.getD []

def admits (t : Wire.Ty) (v : Wire.Val) : Bool := t.atoms.any (Wire.inhabits v)

def encode (t : Wire.Ty) : Ty Nat :=
  (if admits t .vnull then [0] else []) ++
  (if admits t (.vbool true) then [1] else []) ++
  (if admits t (.vbool false) then [2] else [])

def supportedAtom : Wire.Atom → Bool
  | .null | .bool | .boolLit _ => true
  | _ => false

def translate (t : Wire.Ty) : Except String (Ty Nat) :=
  if !t.top && t.atoms.all supportedAtom then .ok (encode t)
  else .error "source type outside the null/boolean/singleton source slice"

def value : Wire.Val → Except String Tm
  | .vnull => .ok .nul
  | .vbool true => .ok .tru
  | .vbool false => .ok .fls
  | _ => .error "source literal outside the null/boolean source slice"

/-- This characterization also rules out extra nonprimitive modeled values. -/
theorem encode_meaning (t : Wire.Ty) (n W v) :
    meaning graph (encode t) n W v ↔
      (admits t .vnull = true ∧ v = .nul) ∨
      (admits t (.vbool true) = true ∧ v = .tru) ∨
      (admits t (.vbool false) = true ∧ v = .fls) := by
  rw [expand_sem]
  cases hn : admits t .vnull <;> cases ht : admits t (.vbool true) <;>
    cases hf : admits t (.vbool false) <;>
    simp [encode, hn, ht, hf, expand, graph, types, primitiveTypes, argumentTypes, semList, Tower.setSem, sem, nulT]

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
    · rename_i b
      cases b <;> cases hv <;> simp [Wire.mem, htop, admits, List.any_eq_true]
  · contradiction

#print axioms translate_exact
end Verification.ExperimentState.SourceTypes
