import Verification.ExperimentState.CellClaims

/-! Bounded free unary function contracts. The initial callable source slice has
one null/boolean primitive argument and result; no optional/rest/this behavior or
object requirements are projected away by this decoder. -/
namespace Verification.ExperimentState.FunctionClaims
open Lean ProgramTyping PositiveRules SourceTypes

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

def translate (j : Json) : Lowering (Ty Nat) := do
  let (D,R) ← signature j
  return [← use (.arrs [(D,R)])]

/-- Exact arrow interpretation, including its contravariant domain, over any
table holding the row. -/
theorem arrow_exact {T : Table} {D R : Ty Nat} (hm : [.arrs [(D,R)]] ∈ T) (n W v) :
    meaning (graph T) [label T (.arrs [(D,R)])] n W v ↔
      arrowT (meaning (graph T) D) (meaning (graph T) R) n W v := by
  rw [label_meaning hm]
  simpa [PositiveNormalization.sem] using
    arrowsT_singleton (meaning (graph T) D) (meaning (graph T) R) n W v

theorem translate_exact {j : Json} {T T' : Table} {F}
    (h : (translate j).run T = .ok (F, T')) (n W v) :
    ∃ D R, signature j = .ok (D,R) ∧ T <+: T' ∧
      (meaning (graph T') F n W v ↔
        arrowT (meaning (graph T') D) (meaning (graph T') R) n W v) := by
  unfold translate at h
  cases hs : signature j with
  | error e => simp [hs, StateT.run, Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift,
      StateT.lift, Except.bind] at h
  | ok DR =>
    obtain ⟨D,R⟩ := DR
    simp only [hs, StateT.run, Bind.bind, StateT.bind, liftM, monadLift, MonadLift.monadLift,
      StateT.lift, Except.bind, Pure.pure, Except.pure, use_run, StateT.pure] at h
    cases h
    refine ⟨D,R,rfl,intern_prefix T _,?_⟩
    exact arrow_exact (mem_intern T _) n W v

#print axioms translate_exact
#print axioms arrow_exact

end Verification.ExperimentState.FunctionClaims
