import Verification.Calculus.Narrowing

/-!
Pins `Calculus/Narrowing.lean`: `narrow` and `tagsOf`.

Not in the trusted base. As with `TypeOperations`, what belongs here is
**precision**: `narrow_sound` is satisfied by a `narrow` that returns its
environment unchanged, and `mem_tagsOf` by a `tagsOf` that returns every
string. Narrowing is the whole point of the calculus, so its precision is
worth pinning where a proof cannot.

The fixtures below are local on purpose. These checks need a type and a
condition, not a well-typed program, so they do not share
`Tests/WellTypedProgram.lean` -- that file is for the three tests that have to
agree about one program.

Not yet covered: the literal and variable-to-variable cases of `narrowEq`,
the truthiness parts, and the `&&`/`||`/`!` cases of `narrow`.
-/

namespace Verification
namespace Tests

open Core

-- The TypeScript type `string | number`.
private def strOrNum : Ty := ofAtoms [.str, .num]

-- A scope holding `x: string | number`.
private def env : TEnv := [("x", strOrNum)]

-- The condition `typeof x === "string"`.
private def cond : Core.Exp := .eq (.tyof (.var "x")) (.lit (.vstr "string"))

/-! ### `typeof x === "string"` narrows both edges -/

-- On the edge where the test holds, `x: string`: `number` is dropped ...
#guard tenvGet (narrow env cond true) "x" == some (ofAtom .str)

-- ... and on the edge where it fails, `x: number`.
#guard tenvGet (narrow env cond false) "x" == some (ofAtom .num)

/-! ### `typeof e` is typed by the tags its operand can carry -/

-- For `string | number` the answer is the literal union `"string" | "number"`,
-- not the whole `string` type.
#guard tagsOf strOrNum == ofAtoms [.strLit "string", .strLit "number"]

end Tests
end Verification
