import Verification.ExperimentState.CallableGraphTests

/-! Recursive callable bags exercise the existing recursive graph interpretation,
producer, consumer, and machine together. The heap may contain the very callable
whose contract describes that heap cell. -/
namespace Verification.ExperimentState.CallableRecursiveTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson

-- R = { bag: null | R; call: Boolean → Boolean }. A second label describes
-- the same recursive contract independently, to exercise cyclic subtyping.
private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [0,2] [] [([1],[1])]],
   [.callable [0,3] [] [([1],[1])]],
   [.callable [0,2,1] [] [([1],[1])]],
   [.arrs [([2],[2])]], [.arrs [([1],[0,2])]]]
private def G : NormalGraph Nat := fun i => types[i]?.getD []
private def labels := List.range types.length
private def pool := vocabulary G labels [] [[0,2],[0,3]]

private def program : Program :=
  [⟨.attach (.var 0) .nul,.bind 1⟩,
   ⟨.write (.var 0) (.var 0),.effect 2⟩,
   ⟨.read (.var 0),.bind 3⟩,
   ⟨.ite (.test .isFun (.var 0)) (.app (.var 0) .fls) .tru,.ret⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[0]⟩,⟨[[2]],[0,2]⟩,⟨[[0,2],[2]],[1]⟩]
private def request : Request := ⟨types,program,claims,[1],0,[]⟩
private def certificate : ControlFlow.Certificate Nat :=
  match produce G labels 10 [1] program claims 0 with | .ok c => c | .error _ => []

theorem checked : checkClosed G [1] program certificate 0 = true := by cbv
#guard match (do
    let response ← produceJson (toJson request) 10
    verifyJson (toJson request) response) with
  | .ok _ => true | .error _ => false

-- Independent recursive labels may be equivalent; adding Boolean to the
-- invariant bag is unsafe even though it widens a read result.
#guard (subtype G pool [2] [3]).isSome
#guard (subtype G pool [3] [2]).isSome
#guard !(subtype G pool [2] [4]).isSome
#guard !(expression G pool 10 [[2]] (.write (.var 0) .tru) [0]).isSome
#guard !(expression G pool 10 [[0,2]] (.app (.var 0) .fls) [1]).isSome

-- Recursive callable values can be higher-order arguments and results.
#guard (expression G pool 10 [] (.funE (.var 0)) [5]).isSome
#guard (expression G pool 10 [[5],[2]] (.app (.var 0) (.var 1)) [2]).isSome

/-- Reading the cyclic bag returns the same callable; its descriptor still
executes identity code. No recursive unfolding is performed by the machine. -/
theorem returns_false : Execution program 14 [] (.at 0 (fun _ => .nul))
    [.fn 0 (.var 0)] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

/-- The getter captures the callable before its bag contains a callable. Calling
it after the self-write observes the updated heap and returns a callable value. -/
private def capturedProgram : Program :=
  [⟨.attach (.var 0) .nul,.bind 1⟩,
   ⟨.funE (.read (.var 1)),.bind 2⟩,
   ⟨.write (.var 1) (.var 1),.effect 3⟩,
   ⟨.app (.var 0) .tru,.bind 4⟩,
   ⟨.ite (.test .isFun (.var 0)) (.app (.var 0) .fls) .tru,.ret⟩]
private def capturedClaims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[6]⟩,⟨[[6],[2]],[0]⟩,⟨[[6],[2]],[0,2]⟩,
   ⟨[[0,2],[6],[2]],[1]⟩]
private def capturedRequest : Request := ⟨types,capturedProgram,capturedClaims,[1],0,[]⟩
#guard match (do
    let response ← produceJson (toJson capturedRequest) 10
    verifyJson (toJson capturedRequest) response) with
  | .ok _ => true | .error _ => false

-- The capture does not freeze the initial null bag. Treating the getter as
-- always returning null must fail its ordinary closure-body obligation.
private def nullGetterG : NormalGraph Nat := fun i =>
  if i == 7 then [.arrs [([1],[0])]] else G i
#guard !(expression nullGetterG (vocabulary nullGetterG (List.range 8) [] []) 10
  [[2]] (.funE (.read (.var 1))) [7]).isSome

theorem captured_returns_false : Execution capturedProgram 18 [] (.at 0 (fun _ => .nul))
    [.fn 0 (.var 0),.nul] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

/-- Certificate acceptance gives safety at every budget, including budgets
beyond the concrete terminating trace; the recursive heap needs no extra axiom. -/
theorem safe (n : Nat) : SafeGraph program (PositiveRules.meaning G [1]) n (ofList []) []
    (.at 0 (fun _ => .nul)) := accepted_closed_safe checked n

theorem coherent {k h s} (run : Execution program k [] (.at 0 (fun _ => .nul)) h s) :
    ∃ D, ObjectCoherence.HeapOk D h ∧ GraphCoherence.StateCoherent D s :=
  GraphCoherence.accepted_closed_coherent checked run

#print axioms checked
#print axioms coherent
#print axioms safe
#print axioms captured_returns_false
#print axioms returns_false
end Verification.ExperimentState.CallableRecursiveTests
