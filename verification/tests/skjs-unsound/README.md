# SKJS unsoundness examples

Runtime counterexamples to declared types. Each entry states whether SKJS
still accepts it or now rejects it after a checker repair.

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

## Repaired: direct writes after compound guards

`compound-write-refinement.ts` retains the two polarities of the #598 runtime
counterexample. SKJS now rejects both singleton returns after invalidating the
field refinement, as TypeScript does. The post-write expression is exported as
Boolean; normal first-error collection aborts before the final loop-exit entry.
The fixture runner requires rejection. `null-tests.mts` and
`write-observations.mts` check the broad read, partial export, and runtime results.

The obsolete diagnostic candidate generator and compound-specific failing-edge
audit have been retired: fresh SKJS exports no longer contain those false claims.
The captured-call witness above still exercises the full failing-edge audit,
and all three mutation-free [controls](../refinement-controls.ts) still verify
in both source formats. Missing-type metadata tests now use the complete valid
`compoundContinue` export, independently of this repaired checker bug.

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
