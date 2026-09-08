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

## Implementation

`model.js` reads structured bundles and adapts legacy comments. `viewer.js` owns
selection, filtering and rendering; `viewer.css` owns layout. `serve.js` runs the
existing producer and report writer. The live path uses the structured manifest;
it does not recover types or source from generated comments. Function `pos` ranges
in manifests use the same original UTF-16 offsets as expression claims.

Run `node verification/tests/report-viewer.js` for model regression checks. They
also run under `make verify`; report-writer tests exercise the manifest producer.

## Editing direction (not implemented)

Claim editing should come first: edit a structured sidecar candidate in the
inspector, retain the original producer snapshot, mark affected results stale,
and verify against unchanged source without rerunning SKJS. Manual edits need
separate provenance. Recollection must not silently overwrite them.

Source editing should use an editor document with decorations, not embedded report
comments. Decorations can move with edits while remaining visibly stale. Changed
or ambiguous attachments must be invalidated. Initially any source edit should
invalidate the file's verification result; finer dependency tracking can follow.
During syntax errors, retain only unambiguous stale decorations. Accept asynchronous
results only for the exact source revision and candidate revision analysed.

Current report IDs identify records within one snapshot. They are not stable
identities across edits; reattachment requires syntax and binding identity as well
as offset mapping. Moving an annotation is not evidence that its claim remains valid.
