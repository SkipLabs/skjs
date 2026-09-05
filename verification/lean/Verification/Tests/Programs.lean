import Verification.Calculus.Programs
import Verification.Tests.WellTypedProgram

/-!
Pins `Calculus/Programs.lean`: the observations (`typeofVal`), the value
environments, and the fuel-indexed evaluator.

**These definitions are in the trusted base, and nothing else in the project
runs them.** The verifier executes `checkFile`, never `evalE` or `execB`; the
program corpus exercises the verifier. `execB` appears in `Verify.lean` only
inside theorem statements. So these checks are the only evidence that the
semantics computes anything at all.

Note that soundness does not constrain it either: `sound` concludes
`execB … ≠ .stuck` and `execB … = .ok v → mem v tr`, both of which hold for an
`execB` that always returns `.timeout`. That is what makes this file load-
bearing rather than decorative.

What belongs here: one case per expression and statement form, both outcomes
of each `.stuck` guard, and the fuel boundary. Build whatever ground terms a
case needs -- a program that gets stuck is as welcome as one that returns.

Not yet covered: `.not`, `.ne`, `.and`, `.or`, `.call` (and so `evalArgs` and
`lookupFun`), `.cst`, and most stuck paths.
-/

namespace Verification
namespace Tests

open Core

/-! ### Fuel -/

#guard evalE [] 0 [] (.lit (.vbool true)) matches .timeout
#guard execB [] 0 [] [] matches .timeout

/-! ### Going wrong -/

-- An unbound variable.
#guard evalE [] 5 [] (.var "x") matches .stuck

-- Falling off the end of a block: the calculus has no way to leave a function
-- other than `return`, and this is where that is enforced.
#guard execB [] 5 [] [] matches .stuck

-- A non-boolean condition.
#guard execB [] 5 [] [.ite (.lit (.vstr "x")) [] []] matches .stuck

/-! ### Observations -/

#guard typeofVal .vnull == "object"
#guard typeofVal .vundef == "undefined"
#guard typeofVal (.vbool true) == "boolean"

/-! ### Environments

`const` shadows rather than replaces, and lookup takes the first match. -/

#guard venvGet (venvSet [("x", .vbool true)] "x" (.vbool false)) "x"
        == some (Val.vbool false)

-- Fewer values than parameters binds nothing; `evalE`'s `.call` guards arity
-- before it gets here. (The parameter type is `unknown`, i.e. `Ty.top`.)
#guard bindParams [("x", { top := true, atoms := [] })] [] == []

/-! ### Running the example program

Both paths return, and both land in the declared return type
(`checked_returns_in_type` says the second part in general). -/

#guard execB exProg 20 (bindParams exFn.params [.vstr "hi"]) exFn.body
        matches .ok (.vstr "hi")

#guard execB exProg 20 (bindParams exFn.params [.vnum 7]) exFn.body
        matches .ok (.vstr "n")

end Tests
end Verification
