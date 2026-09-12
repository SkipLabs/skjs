import Verification.ExperimentState.CallableGraphTests

/-! Calls on union-typed variables use ordinary union elimination. All possible
callables must accept the actual argument; callability alone promises no call. -/
namespace Verification.ExperimentState.CallableUnionTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson

-- The two alternatives have different invariant bags and result types. No
-- auxiliary common arrow label is provided to proof search.
private def types : List (List (Clause (List Nat))) :=
  [[.bool],[.nul],[.callable [0] [] [([0],[0])]],
   [.callable [1] [] [([0],[1])]], [.callable [1] [] [([1],[1])]],
   [.arrs []], [.refs [0] []], [.arrs [([0],[0])]], [.arrs [([0],[1])]] ]
private def G : NormalGraph Nat := fun i => types[i]?.getD []
private def pool := vocabulary G (List.range types.length) [] [[2,3],[0,1]]
private def callClaim : Sequent Nat := ⟨[[2,3]],.app (.var 0) .tru,[0,1]⟩
private def branchProof (F R : Ty Nat) : Evidence Nat :=
  let e := Evidence.node ⟨[F],callClaim.term,R⟩ .callCallable
    [.node ⟨[F],.var 0,F⟩ .var [], .node ⟨[F],.tru,[0]⟩ .tru []]
  .node ⟨[F],callClaim.term,[0,1]⟩ (.sub .subset) [e]
private def proof : Evidence Nat :=
  .node callClaim (.unionVar 0) [branchProof [2] [0],branchProof [3] [1]]
theorem checked : checkTree G proof = true := by cbv

-- Search now derives the same union elimination, without an auxiliary shared
-- constructor view. Each alternative checks the argument and result separately.
#guard (expression G pool 8 callClaim.context callClaim.term callClaim.type).isSome
#guard (expression G pool 8 [[7,8]] (.app (.var 0) .tru) [0,1]).isSome
#guard (expression G pool 8 [[2,8]] (.app (.var 0) .tru) [0,1]).isSome
#guard !(expression G pool 8 [[2,3],[0,1]] (.app (.var 0) (.var 1)) [0,1]).isSome
#guard !(expression G pool 8 [[2,4]] (.app (.var 0) .tru) [0,1]).isSome
#guard !(expression G pool 8 [[2,5]] (.app (.var 0) .tru) [0,1]).isSome
#guard !(expression G pool 8 [[2,6]] (.app (.var 0) .tru) [0,1]).isSome
#guard !(expression G pool 8 [[2,3]] (.app (.var 0) .tru) [0]).isSome

private def program (nullResult : Bool) : Program :=
  [⟨if nullResult then .attach .nul .nul else .attach (.var 0) .tru,.bind 1⟩,
   ⟨.app (.var 0) .tru,.ret⟩]
private def claims : List (PointClaim Nat) := [⟨[],[2,3]⟩,⟨callClaim.context,callClaim.type⟩]
private def request (nullResult : Bool) : Request :=
  ⟨types,program nullResult,claims,[0,1],0,[]⟩
#guard [false,true].all fun nullResult => match (do
    let response ← produceJson (Lean.toJson (request nullResult)) 8
    verifyJson (Lean.toJson (request nullResult)) response) with
  | .ok _ => true | .error _ => false

theorem returns_expected (nullResult : Bool) : Execution (program nullResult) 6 []
    (.at 0 (fun _ => .nul)) [if nullResult then .nul else .tru]
    (.done (if nullResult then .nul else .tru)) := by
  cases nullResult <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.beta rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.ret rfl)

#print axioms checked
#print axioms returns_expected
end Verification.ExperimentState.CallableUnionTests
