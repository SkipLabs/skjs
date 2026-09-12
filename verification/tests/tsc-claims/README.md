# TypeScript's claims, through the verifier

`../../tools/tsc-claims.mts` states what the TypeScript compiler's own checker
believes at every site of a corpus file, as a `stateful-source-v3` document, so
that `tsc` becomes a second claim producer beside SKJS and the same verifier
adjudicates both. `../tsc-claims.mts` runs it over the corpus and pins each
file's verdict.

```sh
node verification/tools/tsc-claims.mts verification/tests/stateful-source/cells.ts --out claims.json
node verification/tests/tsc-claims.mts verification/lean/.lake/build/bin/verifier
```

Sites come from the trusted parser's AST and mirror `SourceClaimJson`'s
`functionSites`; a site's type is `checker.getTypeAtLocation`, and an entry's
environment is each visible binding at `getTypeOfSymbolAtLocation`. A type the
document cannot state is omitted with its reason and `tsc`'s own rendering, in
`<out>.omissions.json`. Every point carries `current: null`: this producer
states types, and leaves current-content assertions to a producer that has
them.

## What the run says

Four fixtures that SKJS rejects verify from `tsc`'s claims with no repair at
all: the two loop exits, the singleton negation, and the arrow intersection.
Where SKJS's own claims needed a hand-written repair at the exit or the
intersection, `tsc`'s flow narrowing carries the fact, and the verifier derives
the annotation from it. That is the comparison this producer exists for.

`skjs-unsound/captured-refinement.ts` is the other direction, and the finding.
`tsc` accepts it with no diagnostic. The verifier, given `tsc`'s own claims,
cannot derive the one at `cell.value` on the line after a callback wrote the
cell: `tsc` kept the refinement from the guard across the call, and the
function returns `false` where it declares `true`. A TypeScript soundness hole,
stated as a failing obligation at the site, with no hand repair anywhere in the
path.

## Reading the corpus column

`examples.mts` shows `tsc accepted→derived` beside SKJS's pair. The column
carries no ⚠, because a `✗` there is as often this producer's limit as a
finding: it states no current-content assertions, so every function that reads
a cell after writing it fails, 56 of 129 in the corpus today. Teaching it to
state the observation TypeScript already computes at that site is the next
step, and would make the column's failures mean what SKJS's do.

`write-refined-read.ts` and `primitive-callbacks.ts` still fail by this producer's
limits: they need a current-content assertion, which it does not write.
`null-guards.ts` now verifies, including independent certificate consumption.
Lambda and allocation claims under union contexts use the expression's own
arrow or cell type. Explicit null tests refine a binding's declared contract
within branches and after an arm that returns; the fallback no longer restores
null at guarded reads or calls. Matching uses symbol identity and stops at
function boundaries. Statement entries use the same declared contracts and
guards even for bindings absent from that statement; `distinctNullableCallbacks`
checks both reference and entry claims. No heap-content
refinement is inferred from these guards.
Where `tsc` rejects the program outright, its claims describe something it does
not accept, and the verifier refusing them says nothing about either checker.
