# SKJS unsoundness examples

Runtime counterexamples to declared types. Each entry states whether SKJS
still accepts it or now rejects it after a checker repair.

## Captured writer

`captured-refinement.ts` is now rejected by SKJS. `staleCapturedCell(true)`
returns `false`, contradicting its declared `true` result. The callback boundary
forgets the field refinement and the return fails against its declared result.
The fixture requires rejection and partial claim collection; the verifier must
not certify that export. The runtime witness and matched control remain tested.
The obsolete failing-heap-edge audit was removed because the checker no longer
exports the stale assertion it audited.
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

## Beyond double precision

`beyond-precision.ts` is accepted by SKJS (issue #781). Its two parameters
are typed with numeric literals that round to the same double, so `x === y`
holds at runtime, yet SKJS treats that branch's input as `never` and admits
returning `x` at a `string` result. The verifier interns both literals as one
singleton and does not derive the string claim; the corpus expects it not to
verify. A runtime witness is not yet recorded here.
