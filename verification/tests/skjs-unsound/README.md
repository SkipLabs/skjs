# SKJS unsoundness examples

Programs accepted by SKJS whose declared types are contradicted by runtime behavior.

## Captured writer

`captured-refinement.ts` is accepted by SKJS. `staleCapturedCell(true)` returns
`false`, contradicting its declared `true` result: a callback writes the captured
cell after the branch test, but SKJS retains the read refinement.

The current verifier distinguishes two checks in `primitive-callbacks.mts`:

1. The actual export reaches a checked incoming-edge obligation for the current
   contents claimed after the callback. Calls discard such observations.
2. A manually weakened candidate forgets only reference read refinements, retaining
   SKJS's expression types. It reaches proof checking and fails at the stale read.

The cross-format witness audit also checks that this is the only failing heap
edge, and that every ordinary obligation checks. The matched control removes the
call, keeps the guard and return read, and verifies with unedited producer claims.
The tests pin the source location and the runtime result. It does not label the
original proof-search failure as a semantic proof that the program is unsound.
`stableSnapshot` in [the primitive callback fixture](../stateful-source/primitive-callbacks.ts) verifies and returns
true: it tests and returns the same immutable value saved before the callback.

## Direct write after a compound guard

`compound-write-refinement.ts` is a verifier-compatible instance of the already
tracked issue #598, covered by `testFieldReassignInBranch` in
[the existing refinement corpus](../../../tests/expect-error/unsound-refinement.ts)
and deep dive F on branch `docs/type-soundness-corpus`. It is not a new bug.
It needs no callback: after the compound loop guard,
`cell.value = false` is followed by a read that SKJS still types as `true`.
`staleCompound(true)` and `staleCompound(false)` both return false despite the
accepted `true` result annotation; null skips the body and returns true. The local
TypeScript checker rejects the stale return.

`null-tests.mts` checks that the original exit-cell union is exported with both
alternatives; Lean absorbs its redundant arm into the existing Boolean invariant.
Standalone current-content assertions inside the loop now reach graph checking. A manual
diagnostic candidate forgets four such observations while preserving the exit union;
the unchanged singleton expression claim then fails proof search. The test also
executes all three inputs. The safe `compoundContinue` example uses a checked
read callback to avoid exporting a retained property refinement; every loop back
edge rechecks its supplied invariant.

The original now reports a located proof obligation; the diagnostic candidate
reports a proof-search failure at the unchanged singleton read. The completed
[audit](../refinement-witnesses.mts) checks every ordinary obligation and heap edge:
exactly one edge fails, at the post-write return assertion. Structurally matched
[controls](../refinement-controls.ts) with the mutation removed verify using fresh
SKJS claims, including the compound and negated guards. Given fresh AST
and raw claims, the shared [candidate generator](compound-write-candidate.js)
prints candidate claims on stdout and exact edits on stderr:

```sh
node verification/tests/skjs-unsound/compound-write-candidate.js \
  ast.json original.json verification/tests/skjs-unsound/compound-write-refinement.ts \
  > candidate.json 2> edits.json
```

These are explicit candidate edits, not automatic widening of SKJS claims. The
source result annotation and stale read claim remain unchanged. The runtime
counterexample is separate from the proof-search failure; verifying the original
function for all admitted inputs requires a source fix.

## Direct write after a negated guard

`staleFlip` in the same `compound-write-refinement.ts` file is another witness of the same #598 defect, through
the negated guard. `!cell.value` refines the read to false, the body writes true,
and the following read is still typed false. SKJS accepts the declared `false`
result and both Boolean inputs return true; null skips the body. TypeScript
rejects the stale return. This covers the opposite refinement outcome from
`compound-write-refinement.ts`, not a new independent unsoundness mechanism.

The exit-cell union is exported with both alternatives and simplifies to the
Boolean invariant. Standalone current-content assertions now reach checked
obligations. `write-observations.mts` checks the complete normal export, the false
claim at the actual post-write read, all three runtime inputs, and the distinction
between an unproved obligation and a runtime counterexample.

## An intersection of arrows collapses to never

`arrow-intersection.ts` is accepted by SKJS with no diagnostic. Its parameter
has an intersection type of two arrows with disjoint domains, which SKJS
computes as `never` (see the matching incompleteness entry), so the parameter
is assumed uninhabited and assigning it to an arrow returning boolean passes.
TypeScript rejects that assignment. `useBoth((x) => null)` returns null against
the declared boolean result. The verifier assumes an arrow parameter at its
annotation, as the caller is held to it, and compares the producer's parameter
claim with that annotation before trying any obligation: SKJS claims the
parameter empty, the annotation says the two-signature arrow, and the function
is refused with "claimed parameter type differs from the source annotation".
The corpus shows this as a parameter claim differing from its annotation, the
finding itself rather than a failed proof search.
