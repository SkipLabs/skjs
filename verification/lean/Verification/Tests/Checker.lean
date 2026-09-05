import Verification.Calculus.Checker
import Verification.Tests.WellTypedProgram

/-!
Pins `Calculus/Checker.lean`: the standalone decision procedure.

Not in the trusted base -- and nothing outside its own module calls it, since
`Verify.lean` has its own traversal. So the program corpus never runs it, and
`checkProg_sound` is satisfied by a checker that rejects everything. These
checks are the only evidence that it accepts anything.

`checkBlock` is defined by well-founded recursion and so does not reduce in
the kernel: this has to be `#guard`, which compiles and runs it, rather than
`by decide`. `Tests/Typing.lean` proves the corresponding fact about the rules.

What belongs here: one accepted program and one rejected one, so that neither
a checker that accepts everything nor one that rejects everything passes.

Not yet covered: a rejection case.
-/

namespace Verification
namespace Tests

open Core

#guard (checkProg exProg matches .ok _)

end Tests
end Verification
