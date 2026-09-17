import Verification.ExperimentState.CallableGraphTests

/-! Higher-order reentry through a callback: the outer call saves a bag read,
then its callback mutates that bag and invokes the same function again. -/
namespace Verification.ExperimentState.CallableReentryTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [1])] [] []],
   [.arrs [([[0]],[1])]], [.arrs [([[4]],[1])]], [.boolLit false]]
private def G : NormalGraph Nat := fun i => types[i]?.getD []
private def labels := List.range types.length

-- At entry: callback, captured bag. The two lets save a read, then a callback
-- result. Returning the saved read and rereading the bag are different programs.
private def body (fresh : Bool) : Tm :=
  .letE (.read (.var 1))
    (.letE (.app (.var 1) .nul) (if fresh then .read (.var 3) else .var 1))
-- At entry: null argument, captured function, captured bag. The nested callback
-- returns false and performs no reentry, so the complete invocation terminates.
private def callback : Tm :=
  .letE (.write (.var 2) .tru) (.app (.var 2) (.funE .fls))
private def program (callable fresh : Bool) : Program :=
  [⟨if callable then .attach (.var 0) .fls else .alloc .fls,.bind 1⟩,
   ⟨.funE (body fresh),.bind 2⟩,
   ⟨.funE callback,.bind 3⟩,
   ⟨.app (.var 1) (.var 0),.ret⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2,3]⟩,⟨[[2,3]],[5]⟩,⟨[[5],[2,3]],[4]⟩,⟨[[4],[5],[2,3]],[1]⟩]
private def request (callable fresh : Bool) : Request :=
  ⟨types,program callable fresh,claims,[1],0,[]⟩

#guard [false,true].all fun callable => [false,true].all fun fresh => match (do
    let r := Lean.toJson (request callable fresh)
    let response ← produceJson r 12
    verifyJson r response) with
  | .ok _ => true | .error _ => false

-- Neither an entry-time read nor the current heap becomes a permanent false
-- result contract for the function; every invocation checks only the invariant.
private def badG : NormalGraph Nat := fun i =>
  if i == 7 then [.arrs [([[4]],[6])]] else G i
private def pool := vocabulary badG (List.range 8) claims []
#guard [false,true].all fun fresh =>
  !(expression badG pool 12 [[2,3]] (.funE (body fresh)) [7]).isSome
-- The reentrant function requires a Boolean-returning callback.
#guard !(expression G (vocabulary G labels claims []) 10 [[5]]
  (.app (.var 0) (.funE .nul)) [1]).isSome

/-- Reentry writes true while the outer frame retains its saved false value.
The fourth heap cell is allocated for the terminating inner callback. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 26 else 24) []
      (.at 0 (fun _ => .nul)) [.tru,.nul,.nul,.nul]
      (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.beta rfl))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.expr (.letV rfl))
      | apply Execution.next (.expr (.letC (.readV rfl)))
      | apply Execution.next (.expr (.letC (.beta rfl)))
      | apply Execution.next (.expr (.letC (.letV rfl)))
      | apply Execution.next (.expr (.letC (.appR rfl (.makeV rfl))))
      | apply Execution.next (.expr (.letC (.letC (.readV rfl))))
      | apply Execution.next (.expr (.letC (.letC (.writeV rfl (by decide)))))
      | apply Execution.next (.expr (.letC (.letC (.beta rfl))))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.ret rfl)

#print axioms returns_expected
end Verification.ExperimentState.CallableReentryTests
