import Verification.Calculus.Typing
import Verification.Tests.WellTypedProgram

/-!
Pins `Calculus/Typing.lean`: that `HasTy`, `BlockOk` and `ProgOk` are
inhabitable.

Not in the trusted base, but this file guards against a specific kind of
vacuity. `Core.sound` reads `ProgOk p → …`. If the rules admitted no
derivation at all -- one rule with an unsatisfiable side condition would do it
-- `sound` would remain a theorem and say nothing. The derivation below is the
witness that it says something.

What belongs here: hand-built derivations, written against the rules rather
than obtained from the checker. `Tests/Checker.lean` covers the decision
procedure; this file covers the rules it decides.

Not yet covered: derivations using `call`, `&&`/`||`, and `const`.
-/

namespace Verification
namespace Tests

open Core

theorem exProg_ok : ProgOk exProg := by
  intro fn hfn
  simp only [exProg, List.mem_singleton] at hfn
  subst hfn
  show BlockOk exProg exFn.params exFn.ret exFn.body
  have hx : HasTy exProg exFn.params (.var "x") exStrOrNum :=
    HasTy.var (t0 := exStrOrNum) (by decide) (by decide)
  have htyof : HasTy exProg exFn.params (.tyof (.var "x")) string_ := HasTy.tyof hx (by decide)
  have hlit : HasTy exProg exFn.params (.lit (.vstr "string")) string_ := HasTy.lit (by decide)
  have hcond : HasTy exProg exFn.params exCond bool_ := HasTy.eq htyof hlit (by decide)
  refine BlockOk.ite hcond ?_ ?_
  · exact BlockOk.ret (HasTy.var (t0 := ofAtom .str) (by decide) (by decide))
  · exact BlockOk.ret (HasTy.lit (by decide))

end Tests
end Verification
