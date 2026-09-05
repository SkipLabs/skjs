import Verification.Lowering
import Verification.Tests.ClaimedPrograms

/-!
Pins `Lowering.lean`: the source-to-graph translation.

**This module is in the trusted base.** The soundness statement is about
`lowerProg funs`, so if the translation is wrong the theorem is about a
different program than the one that was parsed. It had no test file under the
block representation, when it was a one-to-one erasure a reviewer could check
by eye; it is now a label allocator, where an off-by-one yields a well-formed
graph with the wrong control flow.

`Core.Node` derives only `Repr`: Lean cannot derive `DecidableEq` through the
`List Exp` in `Exp.call`, and `native_decide` would add a trust assumption for
a test. So rather than compare whole nodes, these checks project out exactly
the two properties that matter and compare those, which are decidable and say
more plainly what is being pinned.

Two properties matter and neither is visible in the types:

* **Control flow.** A branch whose arm falls through must reach the same
  continuation label as the branch's other edge, so that label has two
  predecessors. That is the join.
* **Lexical binding.** A `const` inside a branch must not be readable after
  it. Slot renaming is what enforces this, and no edge check would catch a
  violation when the two bindings have the same type.

Not yet covered:
any statement relating this to a TypeScript semantics, which does not exist
to be related to.
-/

namespace Verification
namespace Tests

open Core

/-! ### Projections

Whole nodes are not comparable, but their control flow and their slot names
are, and those are what lowering has to get right. -/

private def succs : Core.Node → List (Option Nat)
  | .ret _ => []
  | .set _ _ n => [n]
  | .branch _ y n => [y, n]

private def bound : Core.Node → Option String
  | .set x _ _ => some x
  | _ => none

private partial def readsE : Core.Exp → List String
  | .var x => [x]
  | .lit _ => []
  | .not e | .tyof e => readsE e
  | .eq l r | .ne l r | .and l r | .or l r => readsE l ++ readsE r
  | .call _ args => args.flatMap readsE

private def reads : Core.Node → List String
  | .ret e => readsE e
  | .set _ e _ => readsE e
  | .branch c _ _ => readsE c

/-! ### Both arms return: no join

Node 1 and node 2 are each named once. -/

#guard ((lowerFn narrowingFn).fn.code.map succs) == [[some 1, some 2], [], []]

/-! ### A falling-through arm makes a real join

Node 2 is named by node 1's successor *and* by node 0's false edge -- two
predecessors. Under the block representation the continuation was duplicated
into each arm instead. -/

#guard ((lowerFn mergingFn).fn.code.map succs) == [[some 1, some 2], [some 2], []]

/-! ### Shadowing resolves to distinct slots

The outer `const x` binds `x@0` and the inner one `x@1`, and the `return`
after the branch reads `x@0`. Both are `string`, so this is precisely the case
an edge check cannot catch. -/

#guard ((lowerFn shadowingFn).fn.code.map bound) == [some "x@0", none, some "x@1", none]

#guard ((lowerFn shadowingFn).fn.code.map reads) == [[], ["b"], [], ["x@0"]]

/-! ### The merge is where the branch's binding stops being visible

Node 1 binds `y@0`; node 2, the merge, reads nothing from it. -/

#guard ((lowerFn mergingFn).fn.code.map bound) == [none, some "y@0", none]

/-! ### Both arms falling through: two predecessors, no straight-line path

Node 3 is named by node 1 and by node 2, and by nothing else. Each arm
declares `y`, and they get distinct slots -- sibling scopes, not nested ones,
which the renaming has to separate just the same. -/

#guard ((lowerFn bothFallFn).fn.code.map succs)
        == [[some 2, some 1], [some 3], [some 3], []]

#guard ((lowerFn bothFallFn).fn.code.map bound)
        == [none, some "y@1", some "y@0", none]

/-! ### Nested merges: the inner join is a predecessor of the outer one

Node 4 is reached three ways -- the outer branch's false edge, and both arms
of the inner branch. Under the block representation the continuation would
have been duplicated into each, and the checker would have demanded that
every one of them return. -/

#guard ((lowerFn nestedFn).fn.code.map succs)
        == [[some 1, some 4], [some 3, some 2], [some 4], [some 4], []]

#guard ((lowerFn nestedFn).fn.code.map bound)
        == [none, none, some "q@1", some "p@0", none]

-- Neither inner binding is readable at the merge.
#guard ((lowerFn nestedFn).fn.code.map reads) == [["b"], ["c"], [], [], []]

/-! ### A declaration binds throughout its block, not from its statement on

The `return` before the inner `const x` resolves to the inner slot `x@1`,
which nothing sets on that path -- so the read is an error, as it is in
JavaScript. Resolving from the declaration onward would have silently read
`x@0` instead, and no type check would have noticed. -/

#guard ((lowerFn tdzFn).fn.code.map reads) == [[], ["b"], ["x@1"], ["x@0"]]

/-! ### Dead code is not lowered

The `const x = "inner"` after the `return` has no node: it cannot run. Its
slot is still allocated, which is why the read above resolves to it. -/

#guard ((lowerFn tdzFn).fn.code.map bound) == [some "x@0", none, none, none]

/-! ### And a statement after a `return` in a straight-line body

Only the `return` is lowered, so nothing demands that the `const` have
somewhere to continue to. -/

#guard ((lowerFn deadFn).fn.code.map succs) == [[]]

end Tests
end Verification
