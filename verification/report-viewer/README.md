# Claim report reader

A source-centred inspector for producer claims, collection gaps and recorded
verification results. It is display-only: neither annotations nor stored
verification badges are proof evidence.

## Use

```sh
node verification/report-viewer/serve.js # http://localhost:8731
```

Select an example to collect claims with SKJS, or type any repository-relative
path into **Open any repository path…**; it suggests matching `.ts` sources as
you type, and a full path works whether or not it is listed. The independent
consumer runs whenever a verifier is built — on load, and again after every
applied edit — so nothing is displayed as a result without having been checked.
Rejected programs still show their partial claims and producer diagnostics. Links can select any repository source, for example:
`http://localhost:8731/?file=verification/tests/stateful-source/closures.ts`.

The example groups come from `examples.js`, re-read for each page load, so
adding an example does not need a server restart. Paths outside the repository
are refused, and the listing is a convenience for finding a file, not the limit
of what can be opened.

The address bar follows the view: the selected file, whether it was collected
with verification (`&verify=1`), and the selected claim as `#<manifest id>`
(`#f2x1`, `#f0e3`, `#g0`). Reopening that link restores the same view, and the
id is how a claim can be named in a review or a message. Ids identify records
within one snapshot, not the same claim across edits, so a link into a changed
report may name nothing; the reader then leaves the selection alone rather than
guessing. A linked claim that **Compact** hides is shown with every claim for
that view, without changing the stored density preference.

The server binds to loopback, runs one collection at a time, and applies a
120-second timeout to each subprocess. It rejects source changes detected during
collection and cleans temporary reports up on success and failure.
`SKJS_REPO`, `SKJS_BIN`, `SKJS_IMAGE` and `PORT` configure the local runner.

The HTML can also be opened directly, with its sibling JS and CSS files present.
It then starts empty: there are no bundled example reports, and nothing is shown
until one is read. **Load report…** and drag-and-drop accept either
an annotated `.ts` file or a JSON bundle containing `{source, manifest}`. The
latter preserves exact producer encodings, diagnostics and function ranges.
A manifest alone does not contain source text. Bundle imports check the source
SHA-256 before displaying claims. Annotated-source import is a compatibility
adapter for the display format, with only the data present in those comments.

## Reading dense reports

- The header says whether the producer ran for what is on screen, and when.
  Provenance gives the exact command, how long it took, and whether the
  independent consumer was run. A report read from a file records no such run and
  says so. Every collection runs the producer again; nothing is cached.
- The header tallies what the report records: functions, their recorded statuses,
  and total gaps. Each count moves to the next function it describes, selecting
  that function's failure or first gap. Counts summarize stored outcomes only.
- Find a function by name; selecting it shows its source with original line numbers.
- Keyboard: <kbd>j</kbd>/<kbd>k</kbd> (or the arrow keys) step through the marks
  as drawn, <kbd>[</kbd>/<kbd>]</kbd> change function, <kbd>Esc</kbd> clears the
  selection. Keys are ignored while typing in a field.
- **Compact** shows outer expression claims and environment changes from the
  preceding entry in source order. It hides literal restatements. This is not a
  claim about control-flow edges, narrowing, or the identity of shadowed bindings.
- Claims carry the page: they are tinted and weighted, so they read against the
  code and against the producer's diagnostics beside them.
- Select an expression to see its full type, exact source text, original payload,
  containing statement's entry claims, and nested expression claims.
- **Every claim** includes nested expressions and literal restatements. Multiline
  expressions have a marker on their first line; selection shows the complete span.
- Long types are abbreviated; unfamiliar JSON types say **structured type —
  inspect**, rather than guessing a type from part of their encoding.
- Each function shows both outcomes: **SKJS ✓ · proof ✓**. The first is the
  producer's own outcome for that function, which depends on the source file
  alone and therefore stands until the source changes. The second is what proof
  search found over the claims, which an edit can change: **✓** proved, **✗**
  searched and failed, **?** could not properly try (a claim it needed is
  missing, or the source is outside the fragment), **·** not run. **✗** never
  means the claim is false.
- A disagreement is amber: SKJS accepted a function nothing could prove (which
  is either an unsound acceptance or a limit of these rules, and carries ⚠), or
  SKJS rejected one that a checked certificate covers. Where nothing was
  concluded — a **?** — there is no disagreement to show.
- A verified function carries a stamp. A solid stamp means the independent
  consumer checked a certificate for this report; a dashed one means the status
  was recorded in a file and nothing was checked for what you are looking at.
  Either way it covers the function's modeled obligations, not every claim.
- Provenance spells the producer's snapshot out: complete, or partial because it
  stopped collecting inside that function.
- **SKJS errors** shows the producer's own diagnostics inline, under the exact
  spans they name, including the notes that accompany an error. They describe
  SKJS's run over the source and are neither claims nor verification results.
  Provenance keeps the verbatim text under **Producer diagnostics**, with a count
  and a note about any the source view is not showing — a diagnostic for another
  function in the file, or the tick being off.
- Coverage gaps remain visible in both densities. **Not visited by producer**
  describes collection, not runtime unreachability. Recovery describes the quality
  of a collection snapshot, not necessarily when an individual claim was emitted.
- Function statuses cover modeled obligations, not every displayed producer claim.
  Fingerprints are available under Provenance.

### Why verification stopped

Where the verifier emits a structured obligation diagnostic, the Selection panel
shows what it had and what had to follow: the available slots, the conclusion
required of them, and — for an edge — the same context carried to the
destination, with the differing slots marked and both endpoints selectable. The
role is taken from the record, never guessed from the span: a **return contract**
at a `return` is a different obligation from the returned expression's own claim,
even though they share a span, so a sound claim is not labelled as the culprit. A
mark names its role when the record gives a specific one and stays silent when it
does not.

Types are rendered through the record's own graph table; a clause this reader
does not know is shown as its encoding rather than guessed at, and recursion
through references and arrows stops with an ellipsis. Ids are local to one
attempt: they identify nothing after an edit. The record is explanatory metadata
about an unsuccessful attempt — never evidence, and never a statement that a
claim is false. Failures without a record keep the existing wording. See
[OBLIGATION-DIAGNOSTICS](../OBLIGATION-DIAGNOSTICS.md).

### Verification warnings

When proof search reports an obligation's exact source span, the claim there
reads as it always does and carries the proof symbol after it — **✗** where
search failed, **?** where it could not properly try — the same symbols the
function pill uses. A failed claim is still a claim, so it is not drawn as a
different kind of thing. A banner offers **Show failed obligation**; selection
shows the diagnostic. This is the first reported failure, not an exhaustive
classification of claims. Failure may involve the claimed type, its environment,
a source annotation, or search limitations; the symbol never means the claim has
been disproved.

Incoming-edge failures mark the destination expression whose environment was
not justified. Environment conversion failures mark the statement entry.
Unsupported source expressions carry **?**: conversion stopped before checking
the candidate, so this is not a verdict on an edit.

When verification stopped because a claim it needed is absent, the marker says
so — **verification needed a claim here**, on the gap that already marks that
place, naming the binding when one is missing from an environment. This reports
where extraction stopped, not a claim that was disproved; supplying the claim is
what makes checking possible.

If no source location is available (including older verifier results), the
function-level warning displays the diagnostic directly. The reader never
interprets a graph node number as an expression index. Editing makes prior results
stale and removes their active failure markers until a fresh check completes.

## Implementation

`model.js` reads structured bundles and adapts legacy comments. `obligation.js`
reads an obligation diagnostic into the rows a panel shows. `marks.js`
decides what the source view shows — which claims are drawn at what position,
the outcome symbols, the producer's diagnostic positions — as pure functions the
tests exercise without a browser. `viewer.js` owns selection, events and
rendering; `viewer.css` owns layout. `serve.js` runs the
existing producer and report writer. The live path uses the structured manifest;
it does not recover types or source from generated comments. Function `pos` ranges
in manifests use the same original UTF-16 offsets as expression claims.

Run `node verification/tests/report-viewer.js` for the model and source-mark
regression checks. They
also run under `make verify`; report-writer tests exercise the manifest producer.

## Claim editing

Live reports include an editable candidate in the producer's encoding. There is
no separate workspace panel: select an expression or entry environment and open
**Edit candidate JSON** on it. The original
producer value remains available alongside the editor. **Apply candidate edit**
validates the candidate, checks it, and refreshes the report. A check that
succeeds establishes the modeled obligations for that function; it does not make
the producer's original claims true.

Applying an edit runs the independent consumer against unchanged source, without
rerunning SKJS: an unchecked candidate is never displayed as a result. Editing
conservatively invalidates all function results first. Failed validation leaves the candidate available for correction and the
last successful display marked stale. Source fingerprint changes block checking.
The editor supports expression types and entire entry binding arrays. It uses
JSON; a richer type editor is future work.

Adding a claim happens where the missing one is. Select a coverage gap and the
Selection panel offers the attachment sites inside it; with nothing selected, it
lists the parser-identified expression and statement-entry locations for the
whole function. Enter a type encoding or binding array and apply it. No offsets
need to be entered, and no type is inferred or defaulted. Possible attachment
sites are not necessarily required proof obligations.

Manually added claims have no original producer value; the inspector says so.
After applying, the new claim is selectable and editable normally. Restore removes
all additions along with other manual edits.

A source function with no candidate appears in the function list. Select it and
the panel asks for its `{params, result}` contract. Parameter names and
order come from the source; types use the selected candidate encoding. Adding the
contract reveals that function's missing point-claim sites. No point claims are
invented, and fresh verification checks the contract against source annotations.

**Save report…** writes the source snapshot, candidate, original claims and display
manifest together; **Load report…** reads one back. Both sit with the other
report-wide actions, alongside **Restore original claims**. Unsaved candidate
edits block switching reports until saved or restored. Typed JSON takes effect
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

Loading arbitrary repository source through `?file=relative/path.ts`, or through
the path field, remains supported. No annotated copies are stored in the tree:
the comment-format reader is exercised against reports the test writes in
memory, so nothing generated goes stale against the sources it came from.
