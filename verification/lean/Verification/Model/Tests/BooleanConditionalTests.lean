import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof

namespace Verification.Model.BooleanConditionalTests
open Lean ProgramTyping ProgramCertificates ControlFlow RequestJson PositiveGraphs

/-- 0 true, 1 false, 2 null. -/
private def refinedTypes : List (List (PositiveNormalization.Clause (List Nat))) :=
  [[.boolLit true],[.boolLit false],[.nul]]
private def RG : NormalGraph Nat := .ofRows fun i => (refinedTypes[i]?).getD []
-- A singleton condition checks its own evidence and only the reachable arm.
private def knownCond : Evidence Nat := .node ⟨[],.tru,[0]⟩ .truLit []
private def knownArm : Evidence Nat := .node ⟨[],.fls,[1]⟩ .flsLit []
private def knownTerm : Tm := .ite .tru .fls (.read .nul)
private def knownProof : Evidence Nat :=
  .node ⟨[],knownTerm,[1]⟩ (.ifKnown true) [knownCond,knownArm]
#guard checkTree RG knownProof

private def knownEffectProgram : Program :=
  [⟨.alloc .tru,.bind 1,none⟩,
   ⟨.ite (.letE (.write (.var 0) .fls) .tru) .fls (.read .nul),.ret,none⟩]

/-- Selecting a known arm must not erase the condition's write. -/
theorem known_condition_effects_preserved : Execution knownEffectProgram 8 []
    (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.makeFnV rfl))
    | apply Execution.next (.expr (.iteC (.letC (.writeV rfl (by decide)))))
    | apply Execution.next (.expr (.iteC (.letV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)

#print axioms known_condition_effects_preserved

-- A captured cell is read when the closure is called, after an alias write.
-- Its code is a graph of one node, which reads the capture in its frame's
-- slot 2, past the receiver and the parameter.
private def readCell : Tm := .ite (.read (.var 2)) .tru .fls
private def captureCode : CallCode := .graph 1 [readCell] [(.ret, none)] 0 [.var 0]

/-- The same program, run by the machine. -/
private def captureProgram (q : Bool) : Program :=
  [⟨.alloc .tru,.bind 1,none⟩,
   ⟨.makeFn captureCode .nul,.bind 2,none⟩,
   ⟨.write (.var 1) (if q then .tru else .fls),.effect 3,none⟩,
   ⟨.app (.var 0) .nul,.ret,none⟩]

theorem captured_branch_reads_latest (q : Bool) : Execution (captureProgram q) 16 []
    (.at 0 (fun _ => .nul)) [if q then .tru else .fls,.nul] (.done (if q then .tru else .fls)) := by
  cases q <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.makeFnV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.callGraph rfl (by decide)))
    | apply Execution.next (.expr (.gotoEnter rfl rfl))
    | apply Execution.next (.expr (.frameC (.iteC (.readV rfl))))
    | apply Execution.next (.expr (.frameC .iteT))
    | apply Execution.next (.expr (.frameC .iteF))
    | apply Execution.next (.expr (.frameRet rfl))
    | apply Execution.next (.expr (.iteC (.readV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

#print axioms captured_branch_reads_latest
end Verification.Model.BooleanConditionalTests
