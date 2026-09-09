import Verification.ExperimentState.CellClaims

/-! Bounded free unary function contracts. The initial callable source slice has
one null/boolean primitive argument and result; no optional/rest/this behavior or
object requirements are projected away by this decoder. -/
namespace Verification.ExperimentState.FunctionClaims
open Lean ProgramTyping PositiveRules

structure Signature where
  argument : Wire.Ty
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
  return ⟨← CellClaims.primitive arg, ← CellClaims.primitive (← jField a "result")⟩

/-- Both sides are checked independently; unsupported inputs are never erased. -/
def signature (j : Json) : Except String (Ty Nat × Ty Nat) := do
  let s ← decode j
  return (← SourceTypes.translate s.argument, ← SourceTypes.translate s.result)

def label (D R : Ty Nat) : Nat := SourceTypes.label (.arrs [(D,R)])

def translate (j : Json) : Except String (Ty Nat) := do
  let (D,R) ← signature j
  return [label D R]

theorem label_encode (d r : Wire.Ty) :
    expand SourceTypes.graph [label (SourceTypes.encode d) (SourceTypes.encode r)] =
      [.arrs [(SourceTypes.encode d,SourceTypes.encode r)]] := by
  apply SourceTypes.label_exact
  apply SourceTypes.compound_mem
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨_,SourceTypes.encode_argument_mem d,
    List.mem_map.mpr ⟨_,SourceTypes.encode_mem r,rfl⟩⟩

/-- Exact arrow interpretation, including its contravariant domain. -/
theorem meaning_encode (d r : Wire.Ty) (n W v) :
    meaning SourceTypes.graph [label (SourceTypes.encode d) (SourceTypes.encode r)] n W v ↔
      arrowT (meaning SourceTypes.graph (SourceTypes.encode d))
        (meaning SourceTypes.graph (SourceTypes.encode r)) n W v := by
  rw [expand_sem, label_encode]
  simpa [PositiveNormalization.semList, Tower.setSem, PositiveNormalization.sem] using
    arrowsT_singleton (meaning SourceTypes.graph (SourceTypes.encode d))
      (meaning SourceTypes.graph (SourceTypes.encode r)) n W v

theorem translate_exact {j : Json} {F} (h : translate j = .ok F) (n W v) :
    ∃ D R, signature j = .ok (D,R) ∧
      (meaning SourceTypes.graph F n W v ↔
        arrowT (meaning SourceTypes.graph D) (meaning SourceTypes.graph R) n W v) := by
  unfold translate signature at h
  cases hd : decode j with
  | error e => simp [hd, Bind.bind, Except.bind] at h
  | ok s =>
    cases ha : SourceTypes.translate s.argument with
    | error e => simp [hd,ha, Bind.bind, Except.bind] at h
    | ok D =>
      cases hr : SourceTypes.translate s.result with
      | error e => simp [hd,ha,hr, Bind.bind, Except.bind] at h
      | ok R =>
        simp only [hd,ha,hr,Bind.bind,Pure.pure,Except.bind,Except.pure] at h
        cases h
        refine ⟨D,R,by simp [signature,hd,ha,hr,Bind.bind,Pure.pure,Except.bind,Except.pure],?_⟩
        unfold SourceTypes.translate at ha hr
        split at ha <;> try contradiction
        split at hr <;> try contradiction
        cases ha; cases hr
        exact meaning_encode s.argument s.result n W v

#print axioms translate_exact
#print axioms meaning_encode

end Verification.ExperimentState.FunctionClaims
