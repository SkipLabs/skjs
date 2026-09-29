import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! Higher-order reentry through a callback: the outer call saves a bag read,
then its callback mutates that bag and invokes the same function again. -/
namespace Verification.Model.CallableReentryTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson GraphCodeFixtures

-- At entry: receiver, callback, captured bag. The two lets save a read, then a
-- callback result. Returning the saved read and rereading the bag are different
-- programs.
private def body (fresh : Bool) : Tm :=
  .letE (.read (.var 2))
    (.letE (.app (.var 2) .nul) (if fresh then .read (.var 4) else .var 1))
-- At entry: receiver, null argument, captured function, captured bag. The
-- nested callback returns false and performs no reentry, so the complete
-- invocation terminates.
private def callback : Tm :=
  .letE (.write (.var 3) .tru) (.app (.var 3) (.makeFn (oneNode 1 .fls 0) .nul))
private def program (callable fresh : Bool) : Program :=
  [⟨if callable then .makeAt (oneNode 1 (.var 1) 0) [valueField] [.fls] else .alloc .fls,.bind 1,none⟩,
   ⟨.makeFn (oneNode 1 (body fresh) 1) .nul,.bind 2,none⟩,
   ⟨.makeFn (oneNode 1 callback 2) .nul,.bind 3,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
/-- Reentry writes true while the outer frame retains its saved false value.
The fourth heap cell is allocated for the terminating inner callback. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 34 else 32) []
      (.at 0 (fun _ => .nul)) [.tru,.nul,.nul,.nul]
      (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;> run_machine

#print axioms returns_expected
end Verification.Model.CallableReentryTests
