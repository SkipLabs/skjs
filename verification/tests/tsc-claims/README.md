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
`<out>.omissions.json`. Field reads state their compiler flow type, or retain the field invariant
when the surrounding contextual contract already requests it. For a
primitive field read at statement entry, the receiver binding also carries a
`current` assertion when the flow type differs from the field invariant.
Parentheses, unary operators, and the left side of an equality test preserve
that entry point. Calls, closure bodies, branch arms, and later operands do
not: their observations must not be moved before earlier effects or tests.
Symbol identity selects the receiver binding. Each assertion is untrusted and
must be established by the verifier; no protocol or proof rule is added.

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
carries no ⚠: exporter coverage and proof-search limits still need to be
separated from unsoundness findings. `write-refined-read.ts` now verifies from
TS's original claims. `numericAliasSnapshot` also verifies: the guarded numeric
field read supplies a checked snapshot that survives a later aliased write.
More complex evaluation positions and facts needed across intermediate
statement cuts remain exporter limitations.

`primitive-callbacks.ts` also verifies: an immutable snapshot keeps its
Boolean guard at intervening statement entries even when those statements do
not mention it. The guard is keyed to the snapshot symbol and stops at function
boundaries; this does not preserve a mutable cell refinement across calls.
`null-guards.ts` verifies, including independent certificate consumption.
Lambda and allocation claims under union contexts use the expression's own
arrow or cell type. Explicit null and undefined tests refine a binding's declared contract
within branches and after an arm that returns; the fallback no longer restores
eliminated tags at guarded reads or calls. Removing either absence tag preserves
the other, as checked by `twoAbsenceCapture`. Compound guards combine the
facts of both operands where the outcome establishes both, and preserve the
union of possible paths otherwise. `compoundAbsenceCapture` checks that a
returning absence disjunction excludes both tags before arrow creation. Matching uses symbol identity. Immutable const
captures retain guards from arrow creation; parameters and other function
boundaries stop the walk. Statement entries use the same declared contracts and
guards even for bindings absent from that statement; `distinctNullableCallbacks`
checks both reference and entry claims. No heap-content
refinement is inferred from these guards.
Where `tsc` rejects the program outright, its claims describe something it does
not accept, and the verifier refusing them says nothing about either checker.

Generic identity, annotated copies, distinct rigid parameters and directed bound
chains are exported with function-scoped parameter references and checked by the
same generic source checker as SKJS claims. Saved-evidence mutations test that
false entry/expression claims, unknown binders and missing sites reject.

The corpus configuration uses `moduleDetection: "force"`: separate examples are
independent modules, so repeated function names do not create cross-file overloads
or duplicate implementations. TS acceptance is recorded per function separately
from claim-export availability and proof outcomes. The viewer reads the exported
`.outcomes.json` metadata; it is not admitted as verification evidence.
