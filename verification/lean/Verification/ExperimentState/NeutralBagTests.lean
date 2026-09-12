import Verification.ExperimentState.CallableGraphTests

namespace Verification.ExperimentState.NeutralBagTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson

-- [2,3] describes a Boolean bag without promising whether it is callable.
private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [1] []],[.callable [1] [] []],
   [.callable [1] [] [([1],[1])]]]
private def G : NormalGraph Nat := fun i => types[i]?.getD []
private def pool := vocabulary G (List.range types.length) [] [[2,3]]
private def readClaim : Sequent Nat := ⟨[[2,3]],.read (.var 0),[1]⟩
private def writeClaim : Sequent Nat := ⟨[[2,3]],.write (.var 0) .fls,[0]⟩

-- Both shapes forget into the same bag view; forgetting never changes identity.
#guard (subtype G pool [2] [2,3]).isSome
#guard (subtype G pool [4] [2,3]).isSome
#guard !(subtype G pool [2,3] [4]).isSome

-- The existing consumer can check both branches of ordinary union elimination.
private def readProof : Evidence Nat := .node readClaim (.unionVar 0)
  [.node ⟨[[2]],readClaim.term,[1]⟩ .read [.node ⟨[[2]],.var 0,[2]⟩ .var []],
   .node ⟨[[3]],readClaim.term,[1]⟩ .readCallable [.node ⟨[[3]],.var 0,[3]⟩ .var []]]
private def writeProof : Evidence Nat := .node writeClaim (.unionVar 0)
  [.node ⟨[[2]],writeClaim.term,[0]⟩ .write
     [.node ⟨[[2]],.var 0,[2]⟩ .var [],.node ⟨[[2]],.fls,[1]⟩ .fls []],
   .node ⟨[[3]],writeClaim.term,[0]⟩ .writeCallable
     [.node ⟨[[3]],.var 0,[3]⟩ .var [],.node ⟨[[3]],.fls,[1]⟩ .fls []]]
theorem read_checked : checkTree G readProof = true := by cbv
theorem write_checked : checkTree G writeProof = true := by cbv

-- Search uses the same ordinary union elimination for the receiver slot.
#guard (expression G pool 8 readClaim.context readClaim.term readClaim.type).isSome
#guard (expression G pool 8 writeClaim.context writeClaim.term writeClaim.type).isSome
#guard !(expression G pool 8 [[2,3]] (.app (.var 0) .tru) [1]).isSome
#guard !(expression G pool 8 [[2,3]] (.write (.var 0) .nul) [0]).isSome

-- A bad alternative cannot be hidden by the successful branch.
#guard !(expression G pool 8 [[0,2]] (.read (.var 0)) [1]).isSome
#guard !(expression G pool 8 [[0,2]] (.write (.var 0) .fls) [0]).isSome

-- Both allocation shapes run through one shared graph interface. The neutral
-- view promises no call signature and does not require a runtime shape branch.
private def program (callable : Bool) : Program :=
  [⟨if callable then .attach (.var 0) .tru else .alloc .tru,.bind 1⟩,
   ⟨.write (.var 0) .fls,.effect 2⟩,
   ⟨.read (.var 0),.ret⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2,3]⟩,⟨[[2,3]],[0]⟩,⟨[[2,3]],[1]⟩]
private def request (callable : Bool) : Request :=
  ⟨types,program callable,claims,[1],0,[]⟩
#guard [false,true].all fun callable => match (do
    let response ← produceJson (Lean.toJson (request callable)) 8
    verifyJson (Lean.toJson (request callable)) response) with
  | .ok _ => true | .error _ => false

theorem returns_false (callable : Bool) : Execution (program callable) 9 []
    (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  cases callable <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.writeV rfl (by decide)))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.effect rfl)
      | apply Execution.next (.ret rfl)

#print axioms returns_false
#print axioms read_checked
#print axioms write_checked
end Verification.ExperimentState.NeutralBagTests
