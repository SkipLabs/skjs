import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

set_option maxHeartbeats 3200000

namespace Verification.Model.NeutralBagTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson HeapExpressionRules GraphCodeFixtures

-- [2,3] describes a Boolean bag without promising whether it is callable.
private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [1])] [] [] []],
   [.callable [(valueField, [1])] [] [⟨[6], [[1]], [1], .unrestricted⟩] []], [.boolLit false], [.top]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def pool := vocabulary G (List.range types.length) [] [[2,3]]
private def readClaim : Sequent Nat := ⟨[[2,3]],.read (.var 0),[1]⟩
private def writeClaim : Sequent Nat := ⟨[[2,3]],.write (.var 0) .fls,[0]⟩

-- Both shapes forget into the same bag view; forgetting never changes identity.
#guard (subtype G [2] [2,3]).isSome
#guard (subtype G [4] [2,3]).isSome
#guard !(subtype G [2,3] [4]).isSome

-- The existing consumer can check both branches of ordinary union elimination.
private def readProof : Evidence Nat := .node readClaim (.unionVar 0)
  [.node ⟨[[2]],readClaim.term,[1]⟩ .read [.node ⟨[[2]],.var 0,[2]⟩ .var []],
   .node ⟨[[3]],readClaim.term,[1]⟩ .readCallable [.node ⟨[[3]],.var 0,[3]⟩ .var []]]
private def writeProof : Evidence Nat := .node writeClaim (.unionVar 0)
  [.node ⟨[[2]],writeClaim.term,[0]⟩ .write
     [.node ⟨[[2]],.var 0,[2]⟩ .var [],.node ⟨[[2]],.fls,[1]⟩ .fls []],
   .node ⟨[[3]],writeClaim.term,[0]⟩ .writeCallable
     [.node ⟨[[3]],.var 0,[3]⟩ .var [],.node ⟨[[3]],.fls,[1]⟩ .fls []]]
#guard checkTree G readProof
#guard checkTree G writeProof

-- Search uses the same ordinary union elimination for the receiver slot.
#guard (expression G pool 8 readClaim.context readClaim.term readClaim.type).isSome
#guard (expression G pool 8 writeClaim.context writeClaim.term writeClaim.type).isSome
#guard !(expression G pool 8 [[2,3]] (.app (.var 0) .tru) [1]).isSome
#guard !(expression G pool 8 [[2,3]] (.write (.var 0) .nul) [0]).isSome

-- Every branch's invariant has the field, so typedRead retains facts and links.
#guard bagOperand (expand G [2,3]) == some [(valueField,[1])]
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 readProof) ==
  some (readFrame ⟨[],[],[]⟩ 0 valueField)
#guard match expressionEffect G pool 8 readClaim ⟨[],[],[]⟩ [] [] with
  | some (_, .typedRead 0 _, out) => out == readFrame ⟨[],[],[]⟩ 0 valueField
  | _ => false

-- Nullable and mismatched alternatives cannot borrow the first branch's
-- invariant. Clause order and duplicate valid alternatives do not matter.
#guard bagOperand (expand G [3,2,3]) == some [(valueField,[1])]
#guard bagOperand ([] : List (Clause (List Nat))) == none
#guard bagOperand ([.refs [(valueField, [1])] [] [],.callable [(valueField, [0])] [] [] []] : List (Clause (List Nat))) == none
#guard bagOperand ([.callable [(valueField, [0])] [] [] [],.refs [(valueField, [1])] [] []] : List (Clause (List Nat))) == none
-- A nullable alternative and a mismatched requested invariant must fail.
#guard bagOperand (expand G [0,2]) == none
#guard !HeapExpressionRules.fieldOperand (expand G [0,2]) valueField

-- A bad alternative cannot be hidden by the successful branch.
#guard !(expression G pool 8 [[0,2]] (.read (.var 0)) [1]).isSome
#guard !(expression G pool 8 [[0,2]] (.write (.var 0) .fls) [0]).isSome

-- Both allocation shapes run through one shared graph interface. The neutral
-- view promises no call signature and does not require a runtime shape branch.
/-- A callable bag promising no call: its code names no entry of the table. -/
private def callableBag : Tm := .makeAt (oneNode 1 (.var 0) 0) [valueField] [.tru]
private def program (callable : Bool) : Program :=
  [⟨if callable then callableBag else .alloc .tru,.bind 1,none⟩,
   ⟨.write (.var 0) .fls,.effect 2,none⟩,
   ⟨.read (.var 0),.ret,none⟩]

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

-- A neutral read must preserve the false fact about a different cell.
-- Without that frame, the final Boolean read cannot establish a false singleton.
private def framedProgram (callable : Bool) : Program :=
  [⟨if callable then callableBag else .alloc .tru,.bind 1,none⟩,
   ⟨.fls,.bind 2,none⟩,
   ⟨.alloc (.var 0),.bind 3,none⟩,
   ⟨.read (.var 2),.bind 4,none⟩,
   ⟨.read (.var 1),.ret,none⟩]

theorem framed_returns_false (callable : Bool) : Execution (framedProgram callable) 14 []
    (.at 0 (fun _ => .nul)) [.tru,.fls] (.done .fls) := by
  cases callable <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.ret rfl)

#print axioms framed_returns_false
#print axioms returns_false
end Verification.Model.NeutralBagTests
