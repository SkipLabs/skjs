import Verification.Model.Programs.CertificateProducer
import Verification.Model.Tests.GraphCodeFixtures

/-! Calls on union-typed variables use ordinary union elimination. All possible
callables must accept the actual argument; callability alone promises no call. -/
namespace Verification.Model.CallableUnionTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson GraphCodeFixtures

-- The two alternatives have different invariant bags and result types. No
-- auxiliary common arrow label is provided to proof search.
private def types : List (List (Clause (List Nat))) :=
  [[.bool],[.nul],[.callable [(valueField, [0])] [] [⟨[9], [[0]], [0], .unrestricted⟩] []],
   [.callable [(valueField, [1])] [] [⟨[9], [[0]], [1], .unrestricted⟩] []], [.callable [(valueField, [1])] [] [⟨[9], [[1]], [1], .unrestricted⟩] []],
   [.arrs [] []], [.refs [(valueField, [0])] [] []], [.arrs [⟨[9], [[0]], [0], .unrestricted⟩] []], [.arrs [⟨[9], [[0]], [1], .unrestricted⟩] []],
   [.top], [.undef] ]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def pool := vocabulary G (List.range types.length) [] [[2,3],[0,1]]
private def callClaim : Sequent Nat := ⟨[[2,3]],.app (.var 0) .tru,[0,1]⟩
private def branchProof (F R : Ty Nat) : Evidence Nat :=
  let e := Evidence.node ⟨[F],callClaim.term,R⟩ (.callCallable .unrestricted)
    [.node ⟨[F],.var 0,F⟩ .var [],
     .node ⟨[F],.undef,[9]⟩ (.sub (.fallback [])) [.node ⟨[F],.undef,[10]⟩ .undef []],
     .node ⟨[F],.tru,[0]⟩ .tru []]
  .node ⟨[F],callClaim.term,[0,1]⟩ (.sub .subset) [e]
private def proof : Evidence Nat :=
  .node callClaim (.unionVar 0) [branchProof [2] [0],branchProof [3] [1]]
#guard checkTree G proof

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
  [⟨if nullResult then .makeAt (oneNode 1 .nul 0) [valueField] [.nul]
    else .makeAt (oneNode 1 (.var 1) 0) [valueField] [.tru],.bind 1,none⟩,
   ⟨.app (.var 0) .tru,.ret,none⟩]
theorem returns_expected (nullResult : Bool) : Execution (program nullResult) 8 []
    (.at 0 (fun _ => .nul)) [if nullResult then .nul else .tru]
    (.done (if nullResult then .nul else .tru)) := by
  cases nullResult <;> run_machine

#print axioms returns_expected
end Verification.Model.CallableUnionTests
