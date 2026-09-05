import Verification.Calculus.Types

/-!
Pins `Calculus/Types.lean`: which values inhabit which types.

**These definitions are in the trusted base.** `mem` is the denotation the
soundness theorem concludes with, so a wrong `inhabits` weakens every result
downstream without breaking anything.

What belongs here: cases fixing the denotation, in both directions. A test
that only shows some value inhabits some type would pass for an `inhabits`
that is constantly `true`; each positive case wants a negative one beside it.

`mem` is a `Prop` with no `Decidable` instance, so it takes a one-line proof
rather than `#guard`. Types are written as raw `{top, atoms}` records here
rather than with `ofAtom`/`never`/`unknown`: those live in `TypeOperations`,
one layer up, and this file is pinning the denotation itself.

Not yet covered: `MemAll`, and the literal atoms other than strings.
-/

namespace Verification
namespace Tests

open Core

-- `.str` is the type `string`; `.num` is `number`.
#guard inhabits (.vstr "a") .str
#guard (inhabits (.vstr "a") .num) == false

-- `.strLit "a"` is the literal type `"a"`, denoting exactly one value.
#guard inhabits (.vstr "a") (.strLit "a")
#guard (inhabits (.vstr "b") (.strLit "a")) == false

-- `never` (no atoms, not top) denotes nothing ...
example : ¬ mem (Val.vstr "a") { top := false, atoms := [] } := by
  rintro (h | ⟨_, h, _⟩) <;> simp_all

-- ... `unknown` (top) denotes everything ...
example : mem (Val.vstr "a") { top := true, atoms := [] } := .inl rfl

-- ... and `string` denotes the strings.
example : mem (Val.vstr "a") { top := false, atoms := [.str] } :=
  .inr ⟨.str, by simp, rfl⟩

end Tests
end Verification
