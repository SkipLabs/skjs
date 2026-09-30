import Verification.Model.Source.RequestJson
import Verification.Model.Tests.GraphCodeFixtures

/-! A closure mutates a captured neutral bag. Invocation invalidates current
contents and read links while preserving immutable snapshots. -/
namespace Verification.Model.CallableMutationTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow HeapExpressionRules GraphCodeFixtures

/-- The mutator writes the captured bag, its frame's slot 3, past its receiver
and parameter. -/
private def mutator : Tm := .write (.var 3) .tru
private def program (callable fresh : Bool) : Program :=
  [⟨.fls,.bind 1,none⟩,
   ⟨if callable then .makeAt (oneNode 1 (.var 0) 1) [valueField] [.var 0] else .alloc (.var 0),.bind 2,none⟩,
   ⟨.read (.var 0),.bind 3,none⟩,
   ⟨.makeFn (oneNode 1 mutator 3) .nul,.bind 4,none⟩,
   ⟨.app (.var 0) .nul,.effect 5,none⟩,
   ⟨if fresh then .read (.var 2) else .var 1,.ret,none⟩]
/-- The heap really changes to true; a saved immutable value remains false.
Creation of the mutator accounts for the second, null-initialized heap cell. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 20 else 19) []
      (.at 0 (fun _ => .nul)) [.tru,.nul] (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.makeFnV rfl))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.expr (.writeV rfl (by decide)))
      | apply Execution.next (.expr (.callGraph rfl (by decide)))
      | apply Execution.next (.expr (.gotoEnter rfl rfl))
      | apply Execution.next (.expr (.frameC (.writeV rfl (by decide))))
      | apply Execution.next (.expr (.frameRet rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.effect rfl)
      | apply Execution.next (.ret rfl)

#print axioms returns_expected
end Verification.Model.CallableMutationTests
