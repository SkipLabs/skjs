import Verification.ExperimentState.CellClaims

/-! Bounded free unary function contracts. The initial callable source slice has
one null argument and a primitive result; no optional/rest/this behavior or
object requirements are projected away by this decoder. -/
namespace Verification.ExperimentState.FunctionClaims
open Lean ProgramTyping PositiveRules

structure Signature where
  result : Wire.Ty

def decode (j : Json) : Except String Signature := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is not a function signature"
  let [a] ← jArr j "atoms" | throw "expected a single function atom"
  CellClaims.fieldsExactly a ["a","params","result","construct","array"]
  if (← jStr (← jField a "a")) != "function" then throw "expected a function atom"
  for key in ["construct","array"] do
    let mode ← jStr (← jField a key)
    if mode != "unknown" && mode != "absent" then throw "unsupported function object mode"
  let [arg] ← jArr a "params" | throw "expected one required function parameter"
  let A ← SourceTypes.translate (← CellClaims.primitive arg)
  if A != [0] then throw "source closures currently require a null argument"
  return ⟨← CellClaims.primitive (← jField a "result")⟩

def result (j : Json) : Except String (Ty Nat) := do
  SourceTypes.translate (← decode j).result

def label (A : Ty Nat) : Nat := 8 + CellClaims.referenceLabel A

def translate (j : Json) : Except String (Ty Nat) := do
  return [label (← result j)]

theorem label_encode (t : Wire.Ty) :
    expand SourceTypes.graph [label (SourceTypes.encode t)] =
      [.arrs [([0],SourceTypes.encode t)]] := by
  cases hn : SourceTypes.admits t .vnull <;>
    cases ht : SourceTypes.admits t (.vbool true) <;>
    cases hf : SourceTypes.admits t (.vbool false) <;>
    simp [label, CellClaims.referenceLabel, SourceTypes.encode, hn, ht, hf,
      expand, SourceTypes.graph, SourceTypes.types]

/-- Exact constructor interpretation; no semantic normalization of arrows. -/
theorem meaning_encode (t : Wire.Ty) (n W v) :
    meaning SourceTypes.graph [label (SourceTypes.encode t)] n W v ↔
      arrowT (meaning SourceTypes.graph [0]) (meaning SourceTypes.graph (SourceTypes.encode t)) n W v := by
  rw [expand_sem, label_encode]
  simpa [PositiveNormalization.semList, Tower.setSem, PositiveNormalization.sem] using
    arrowsT_singleton (meaning SourceTypes.graph [0])
      (meaning SourceTypes.graph (SourceTypes.encode t)) n W v

theorem result_checked {j : Json} {A} (h : result j = .ok A) :
    ∃ s, decode j = .ok s ∧ SourceTypes.translate s.result = .ok A := by
  unfold result at h
  cases hd : decode j with
  | error e => simp only [hd] at h; contradiction
  | ok s =>
    simp only [hd] at h
    exact ⟨s,rfl,h⟩

theorem translate_exact {j : Json} {F} (h : translate j = .ok F) (n W v) :
    ∃ A, result j = .ok A ∧
      (meaning SourceTypes.graph F n W v ↔
        arrowT (meaning SourceTypes.graph [0]) (meaning SourceTypes.graph A) n W v) := by
  unfold translate at h
  cases hr : result j with
  | error e => simp only [hr] at h; contradiction
  | ok A =>
    simp only [hr] at h
    change Except.ok [label A] = Except.ok F at h
    cases h
    refine ⟨A,rfl,?_⟩
    obtain ⟨s,_,ht⟩ := result_checked hr
    unfold SourceTypes.translate at ht
    split at ht
    · cases ht
      exact meaning_encode s.result n W v
    · contradiction

#print axioms translate_exact
#print axioms meaning_encode

end Verification.ExperimentState.FunctionClaims
