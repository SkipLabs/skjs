# Claim report reader

A source-centred inspector for producer claims, collection gaps and recorded
verification results. It is display-only: neither annotations nor stored
verification badges are proof evidence.

## Use

```sh
node verification/report-viewer/serve.js # http://localhost:8731
```

Select a source file to collect claims with SKJS. Tick **verify** to run the
independent consumer. Rejected programs still show their partial claims and
producer diagnostics. Links can select any repository source, for example:
`http://localhost:8731/?file=verification/tests/stateful-source/closures.ts`.

The server binds to loopback, runs one collection at a time, and applies a
120-second timeout to each subprocess. It rejects source changes detected during
collection and cleans temporary reports up on success and failure.
`SKJS_REPO`, `SKJS_BIN`, `SKJS_IMAGE` and `PORT` configure the local runner.

The HTML can also be opened directly, with its sibling JS and CSS files present.
It includes two example reports. **Load report** and drag-and-drop accept either
an annotated `.ts` file or a JSON bundle containing `{source, manifest}`. The
latter preserves exact producer encodings, diagnostics and function ranges.
A manifest alone does not contain source text. Bundle imports check the source
SHA-256 before displaying claims. Annotated-source import is a compatibility
adapter for the display format, with only the data present in those comments.

## Reading dense reports

- Find a function by name; selecting it shows its source with original line numbers.
- **Compact** shows outer expression claims and environment changes from the
  preceding entry in source order. It hides literal restatements. This is not a
  claim about control-flow edges, narrowing, or the identity of shadowed bindings.
- Select an expression to see its full type, exact source text, original payload,
  containing statement's entry claims, and nested expression claims.
- **Every claim** includes nested expressions and literal restatements. Multiline
  expressions have a marker on their first line; selection shows the complete span.
- Long types are abbreviated; unfamiliar JSON types say **structured type —
  inspect**, rather than guessing a type from part of their encoding.
- The optional program-point table compares environments in source order. Its
  line buttons select the corresponding entry claim.
- Coverage gaps remain visible in both densities. **Not visited by producer**
  describes collection, not runtime unreachability. Recovery describes the quality
  of a collection snapshot, not necessarily when an individual claim was emitted.
- Function statuses cover modeled obligations, not every displayed producer claim.
  Fingerprints are available under Provenance.

### Verification warnings

When proof search reports an expression obligation's exact source span, that
claim gets an amber **⚠ proof not established** marker in both density modes.
A banner offers **Show failed obligation**; selection shows the diagnostic.
This is the first reported failure, not an exhaustive classification of claims.
Failure may involve the claimed type, its environment, a source annotation, or
search limitations; the marker does not mean the claim has been disproved.

Incoming-edge failures mark the destination expression whose environment was
not justified. Environment conversion failures mark the statement entry.
Unsupported source expressions instead say **unsupported source**: conversion
stopped before checking the candidate, so this is not a verdict on an edit.

If no source location is available (including older verifier results), the
function-level warning displays the diagnostic directly. The reader never
interprets a graph node number as an expression index. Editing makes prior results
stale and removes their active failure markers until a fresh check completes.

## Implementation

`model.js` reads structured bundles and adapts legacy comments. `viewer.js` owns
selection, filtering and rendering; `viewer.css` owns layout. `serve.js` runs the
existing producer and report writer. The live path uses the structured manifest;
it does not recover types or source from generated comments. Function `pos` ranges
in manifests use the same original UTF-16 offsets as expression claims.

Run `node verification/tests/report-viewer.js` for model regression checks. They
also run under `make verify`; report-writer tests exercise the manifest producer.

## Claim editing

Live reports include an editable candidate in the producer's encoding. Select an
expression or entry environment and open **Edit candidate JSON**. The original
producer value remains available alongside the editor. **Apply candidate edit**
validates the candidate and refreshes the report; it does not establish the claim.

**Verify candidate** runs the existing independent consumer against unchanged
source, without rerunning SKJS. Editing conservatively invalidates all function
results. Failed validation leaves the candidate available for correction and the
last successful display marked stale. Source fingerprint changes block checking.
The editor supports expression types and entire entry binding arrays. It uses
JSON; a richer type editor is future work.

**Add missing claim…** lists parser-identified expression and statement-entry
locations in the selected function. Select a site, enter its type encoding or
binding array, and apply it. Selecting a collection gap offers the sites within
that gap. No offsets need to be entered, and no type is inferred or defaulted.
Possible attachment sites are not necessarily required proof obligations.

Manually added claims have no original producer value; the inspector says so.
After applying, the new claim is selectable and editable normally. Restore removes
all additions along with other manual edits.

A source function with no candidate appears in the function list. Select it and
choose **Add missing claim…** to supply `{params, result}`. Parameter names and
order come from the source; types use the selected candidate encoding. Adding the
contract reveals that function's missing point-claim sites. No point claims are
invented, and fresh verification checks the contract against source annotations.

**Export bundle** saves the source snapshot, candidate, original claims and display
manifest together. Import it with **Load report** to continue. Unexported candidate
edits block switching reports until exported or restored. Typed JSON takes effect
only on **Apply**; switching selections discards unapplied textarea edits.
**Restore original claims** restores the baseline and clears verification results.
Neither operation writes the source file or replaces the producer's claim file.

The candidate wrapper is `{format, file, sourceSha256, claims}`. Supported formats
are `skjs` and `source-claims`; the latter uses the existing normalized sidecar
language. For CLI use, save the `claims` member and pass it to `annotate-source.js`
with the matching `--format`. Legacy annotated-only reports are read-only because
they do not preserve a verifier input. Live candidate verification requires the
local server; standalone viewing and bundle export remain available offline.

`candidate.js` handles immutable candidate updates; `editor.js` owns the editing
workspace and its revision/verification lifecycle. The server's JSON POST
`/api/candidate` validates source identity and invokes the existing report writer
and optional verifier. Candidate inputs and stored results are never trusted proof
evidence. The candidate tests exercise real verification with a deliberately
unavailable producer binary, a false claim, and a stale source fingerprint.

## Source editing direction (not implemented)

Source editing should use an editor document with decorations, not embedded report
comments. Decorations can move with edits while remaining visibly stale. Changed
or ambiguous attachments must be invalidated. Initially any source edit should
invalidate the file's verification result; finer dependency tracking can follow.
During syntax errors, retain only unambiguous stale decorations. Accept asynchronous
results only for the exact source revision and candidate revision analysed.

Current report IDs identify records within one snapshot. They are not stable
identities across edits; reattachment requires syntax and binding identity as well
as offset mapping. Moving an annotation is not evidence that its claim remains valid.

## Example selection

The live picker defaults to **Current verifier examples**, tested by the same
source suites as `make verify`. **Claim repair** contains the deliberately
rejected partial-collection exercise. **Unsupported examples** contains expected
source limitations and never implies those programs are verified.

The standalone samples also use current fixtures: `basic.ts` (recorded verified
functions) and `partial-claims.ts` (a mix of missing claims and a verified function).
Their stored statuses are report data, not fresh evidence. Loading arbitrary
repository source through `?file=relative/path.ts` remains supported.
