import Verification.Calculus.TypeOperations

/-!
Pins `Calculus/TypeOperations.lean`: `sub`, `meet` and `diff`.

These definitions are *not* in the trusted base -- a bug in them causes a
rejection or a failed proof, never an unsound acceptance.

What belongs here is therefore **precision, not soundness**. Soundness is
already proved (`sub_sound`, `meet_sound`, `diff_sound`), and every one of
those proofs is satisfied by a degenerate implementation: a `sub` that always
returns `false` is sound, a `diff` that drops nothing is sound. Only executable
cases distinguish the real thing from the useless one.

Not yet covered: `meet`, the numeric and boolean literal atoms, and the `top`
cases.
-/

namespace Verification
namespace Tests

open Core

/-! ### `ofAtoms` builds the union, and agrees with `ofAtom` on singletons -/

#guard ofAtoms [.str] == ofAtom .str
#guard ofAtoms [] == never

/-! ### `sub` accepts what it should, and rejects what it should -/

-- `"a" <: string`, but not the other way round.
#guard sub (ofAtom (.strLit "a")) (ofAtom .str)
#guard !sub (ofAtom .str) (ofAtom (.strLit "a"))

-- `never <: string <: unknown`, and `unknown` is not a subtype of `string`.
#guard sub never (ofAtom .str)
#guard sub (ofAtom .str) unknown
#guard !sub unknown (ofAtom .str)

/-! ### `diff` removes an atom, and leaves an unrelated one alone -/

-- `(string | number) \ string` is `number`.
#guard diff (ofAtoms [.str, .num]) (ofAtom .str) == ofAtom .num

-- `number \ string` is still `number`.
#guard diff (ofAtom .num) (ofAtom .str) == ofAtom .num

end Tests
end Verification
