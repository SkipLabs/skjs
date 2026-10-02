# TypeScript's claims, through the verifier

`../../tools/tsc-claims.mts` states what the TypeScript compiler's own checker
believes at every site of a corpus file, as a source-claims document, so that
`tsc` is a claim producer the same verifier adjudicates. It runs through the
pipeline entry point, which the corpus (`corpus-report.mts`) calls on every corpus
file and the report viewer on the file it opens:

```sh
node verification/pipeline/verify-source.mts verification/tests/stateful-source/cells.ts --producer tsc
```

Sites come from the trusted parser's AST and mirror `SourceClaimJson`'s
`functionSites`; a site's type is `checker.getTypeAtLocation`, and an entry's
environment is each visible binding at `getTypeOfSymbolAtLocation`. A type the
document cannot state is omitted with its reason and `tsc`'s own rendering, in
the run's `omissions.json`. Field reads state their compiler flow type, or retain the field invariant
when the surrounding contextual contract already requests it. For a
primitive field read at statement entry, the receiver binding also carries a
`current` assertion when the flow type differs from the field invariant.
Parentheses, unary operators, and the left side of an equality test preserve
that entry point. Calls, closure bodies, branch arms, and later operands do
not: their observations must not be moved before earlier effects or tests.
Symbol identity selects the receiver binding. Each assertion is untrusted and
must be established by the verifier; no protocol or proof rule is added.

## Reading the corpus column

`corpus-report.mts` shows `tsc accepted→derived` per function. Exporter coverage
and proof-search limits are not separated from unsoundness findings, so a
`✗` on the right is no verdict about TypeScript. Where `tsc` rejects the
program outright, its claims describe something it does not accept, and the
verifier refusing them says nothing about either checker. More complex
evaluation positions and facts needed across intermediate statement cuts are
exporter limitations.

The corpus configuration uses `moduleDetection: "force"`: separate examples are
independent modules, so repeated function names do not create cross-file overloads
or duplicate implementations. TS acceptance is recorded per function separately
from claim-export availability and proof outcomes. The run writes it to
`tsc-verdicts.json`, which the corpus and the report viewer read; it is not admitted as
verification evidence.
