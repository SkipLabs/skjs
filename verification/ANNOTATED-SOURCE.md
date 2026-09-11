# Annotated source reports

`tools/annotate-source.mts` writes a separate TypeScript copy showing producer
claims, optionally with freshly checked function results. It also writes a JSON
manifest preserving the claims, diagnostics and content fingerprints. Producer
names are reported provenance, not authenticated identities. The original source and claim files are not modified. Existing output files are
never overwritten.

```sh
node verification/tools/annotate-source.mts input.ts \
  --claims claims.json --producer skjs \
  --verify verification/lean/.lake/build/bin/verifier
```

The default outputs are `input.annotated.ts` and `input.annotated.ts.json`.
`--out /path/report.ts` chooses another destination. The claims file is an
existing SKJS `--emit-skjs-type-claims` export. `--file-key` selects its file key
if that differs from the input path. The command does not rerun SKJS or alter
its claims. Omit `--verify` to generate a claims-only report; use `--depth N` to
set proof-search depth (default 10).

A typical excerpt looks like:

```ts
/* @verify-report kind=function; id=f0; function copyTrue; producer=skjs; claimed () => boolean; verification=verified */
function copyTrue(): boolean {
  /* @verify-report kind=entry; id=f0e0; entry { x: true } @57:77 */
  const y: boolean = /* @verify-report kind=expression; id=f0x0; expr true @76:77 */ x;
  return y;
}
```

This excerpt illustrates the notation, not a complete program. The real report
includes all exported entries and expressions, including unused bindings. Spans
refer to the original source before annotation.

## Machine-readable fields

Every annotation begins with `name=value; ` fields, before prose written for
people. The header lists them as `annotation-fields`, so a reader can tell which
fields a report was written with. A consumer should read the fields and treat the
prose as text that may be reworded.

| Field | On | Meaning |
| --- | --- | --- |
| `kind` | every annotation | `function`, `entry`, `expression` or `gap`. |
| `id` | every annotation | Joins this mark to its record in the manifest: `f0`, `f0e3`, `f0x7`, `g2`. |
| `reason` | gaps | Why nothing is claimed here, as a stable slug: `statement-not-visited`, `expression-without-type`, `claims-unavailable`, `claim-edit`. |
| `unsupported` | entries | Bindings in that environment whose exported payload could not be decoded, joined by `+`. |

Manifest records carry the same `id`, so a tool can display a mark and look up
its exact producer payload without matching on positions or prose.

Types are displayed in surface syntax: primitive names, literals as the literal
(`"string"`, `3`, `true`), unions as `a | b`, cells as `{ value: boolean }`, and
arrows as `(boolean) => null`. A cell whose read and write types differ shows
both (`{ value: read true write boolean }`), because that distinction is exactly
what a stale refinement looks like and TypeScript has no shape for it.
`tools/claim-types.js` does this printing, and the reader uses the same module,
so a comment and a panel never disagree.

The displayed text is a **view of the claim, not an encoding of it**. Surface
syntax does not show index signatures, callable shapes or per-field optionality,
so reading a type back requires the claim it came from: what the text names is
replaced, and what it does not name comes from that original. A shape the
printer cannot name is written verbatim as JSON rather than summarized, so no
requirement is silently hidden. A binding the producer could not decode has no
claimed type at all and reads `(unavailable)`; it is named in the `unsupported`
field rather than given an invented type.

**The manifest keeps the producer's exact payloads** in `raw`, whatever the
comment shows. Claim identity, certificates and verification results depend on
those, never on the display text. Changing how a type is printed changes the
bytes of newly generated annotated files, and therefore their `annotatedSha256`;
snapshots generated earlier stay valid against the hashes recorded with them, and
source, claim and certificate identities are unaffected.

A failed function result may include `location: {kind: "expression-obligation",
pos: [start, end]}` when the verifier reports an exact source span. This locates
the first failed proof-search obligation, not a proof that the claim is false
or an exhaustive list of invalid claims. Without a location, readers must keep
the warning at function level; graph labels are not source expression indexes.
Other location kinds are `edge-obligation` (the destination expression span),
`environment-obligation` (a statement-entry `start` offset), and
`source-limitation` (an unsupported source expression span). The last indicates
source conversion stopped before proof checking; it is not a failed claim.

A proof-search failure can additionally include `obligation`, a version-1 structured
record described in [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md). It identifies
the actual sequent or selected mapped edge, with extraction-provided roles and
source provenance. Prefer it to guessing a failure role from `location` or the
TypeScript AST. The old `location` remains a fallback for readers without support
and for failures not yet carrying structured metadata. No record is evidence
that a claim is false or that an individual premise has been proved.

Two kinds report a claim the extractor needed and did not find, which is a
different finding from a search that failed: `missing-expression-claim` (the
expression span with no claimed type) and `missing-environment-claim` (a
statement-entry `start`, with the `binding` name when one named binding is
absent from a supplied environment). A report usually already marks these places
as gaps; the location says which gap verification stopped at. Supplying the
claim is what makes checking possible, and establishes nothing by itself.

The manifest also exposes `missingFunctions`: source declarations without a
function candidate, with `name`, `namePos`, full `pos`, parameter names in source
order, and `missingSites`. These are parser-derived repair hints, not inferred
types or verified facts. The reader validates their spans before presenting them;
adding a contract still requires fresh source-based checking.

Manifest functions also expose `missingSites`: parser-identified expression and
statement-entry spans without a candidate claim, each with a `kind` (`expression`
or `environment`) and `syntax` label. These are possible attachment locations,
not a declaration that verification needs a claim at every one. A reader may use
them for manual repair; the source adapter and verifier still validate the input.

Manifest functions include a `pos: [start, end]` range for the full source function,
using original UTF-16 offsets. A reader can therefore focus a function without
reconstructing its boundaries from display comments.

`--stdout json` writes `{"annotated": …, "manifest": …}` to standard output and
creates no files, for callers that render a report without keeping one.

## Reading a report

`report-viewer/claim-report-viewer.html` reads an annotated file and draws each
claim as a bracket under the span it is about, with a table of how the bindings
narrow. It is a reader for this output, with the same standing: display only.
Its companion `report-viewer/serve.js` runs SKJS and this generator on a chosen
file so a report can be produced and read in one step. See
[report-viewer/README.md](report-viewer/README.md).

## What verification results mean

With `--verify`, the tool parses the current source with the maintained source
adapter, generates a certificate for each reported function, then invokes the
independent consumer on that certificate. It never accepts stored status fields
as evidence. Results are attached to functions, not to individual raw export
entries: the compiler can legitimately ignore unrelated bindings such as
implicit `this`, so a verified function does not prove every displayed claim.

| Status | Meaning |
| --- | --- |
| `not-run` | Claims are displayed; no verification was requested. |
| `verified` | Fresh evidence passed the independent consumer for the modeled function and its required claims. |
| `not-established` | Production or consumption did not establish those obligations; the diagnostic is retained. This does not prove the claim false. |
| `unsupported` | The source parser's fragment gate rejected the file. No function certificate was checked. |

The source parser currently gates the file before per-function checking, so an
unsupported construct can prevent results for other functions in that file.
Unsupported type claims encountered later can appear as `not-established` with
the decoder's diagnostic. Operational failures, such as missing tools or a
subprocess timeout, fail the report command instead of becoming type results.
No `refuted` status is emitted: this tool does not construct counterexamples.

Successful command exit means a report was written, not that every function was
verified. Inspect the results array in its manifest for automation.

## Other producers

A producer-independent display format is supported with `--format report`:

```json
{
  "version": 1,
  "source": {"file": "input.ts", "sha256": "SHA256_OF_SOURCE_BYTES"},
  "producer": "another-analyzer",
  "functions": [{
    "name": "f",
    "namePos": [9, 10],
    "entries": [{"pos": [34, 43], "bindings": [{"name": "x", "type": "boolean"}]}],
    "expressions": [{"pos": [41, 42], "type": "boolean"}]
  }]
}
```

Offsets are UTF-16 indices, as in the TypeScript AST; the illustrative offsets
above must be replaced with the exact positions in the supplied file. Expression
spans must match AST nodes, and entry starts must be AST boundaries in the named
function. Duplicate attachments and stale source fingerprints are rejected.
Type strings are producer descriptions, not parsed type assertions. Optional
`raw` fields on bindings and expressions preserve additional producer data.

```sh
node verification/tools/annotate-source.mts input.ts \
  --format report --claims display-claims.json --out report.ts
```

Generic report inputs are claims-only. Their stored status fields are ignored;
`--verify` is rejected until that producer has a verification adapter. This
versioned display format is distinct from the semantic source-claim interface
proposed in [CLAIM-INTERFACE](CLAIM-INTERFACE.md). It is not a shortcut around
normalizing and checking a new producer's types.

## Freshness and source preservation

The manifest records the source and claims digests, the annotated output digest,
and, for checked reports, the verifier executable, parser and certificate
digests. Check the saved snapshot against the current local files with:

```sh
node verification/tools/annotate-source.mts --check-fresh input.annotated.ts
```

This detects changed source, claims, annotated output, parser or verifier. It is
neither certificate checking nor authentication of a manifest. A stored result
must always be freshly checked before it is relied upon. Certificates themselves
are temporary; their identities and outcomes are retained in the manifest.

Annotations are marked `@verify-report`, not the proposed `@verify entry` or
`@verify expr` input directives. Reusing an already annotated copy as the original
source is rejected. Report comments are never consumed by the Lean checker.
The renderer escapes comment delimiters and line terminators in producer text,
and compares the original and annotated TypeScript ASTs, including token text.
Expression annotations introduce no new line breaks, preserving `return` and
other automatic-semicolon behavior. This is a display transformation, not a
proof of the separate source-to-calculus lowering.

`make verify` runs the report regressions against a real SKJS closure export:
attachment, Unicode, stale snapshots, comment injection, source preservation,
independent verification, and false claims reported as not established.

## Rejected programs and partial collection

Ordinary `skjs check --emit-skjs-type-claims` retains the claims collected before
an error aborts a function body. It rethrows the same error: export does not
change the checker’s stopping policy, diagnostics or exit status. Other
independent definitions can still have complete snapshots.

Each exported function includes `collection` metadata:

- `completion`: `complete` or `aborted` describes collection, not verification.
- `mode`: `normal`, `keep-going` or `backtrace` records the checker mode.
- `quality`: `unverified` normally; `recovery` if checking continued through a
  reported error in that function. Recovery labels apply to the whole snapshot,
  since later inference can affect types collected earlier.
- `visitedExpressions`: original spans entered by expression checking, including
  expressions that failed before a result could be recorded.

Reports show entered expressions without a result and, for aborted snapshots,
unvisited supported statements. A function without a snapshot is labeled
“claims unavailable”: failures during signature setup or before body checking
can leave no snapshot. Parser failures may leave no usable file export at all.
Older exports without collection metadata do not imply any visitation history.

Keep the ordinary first-error mode for normal use. `--keep-going` remains an
explicit option for debugging and exploratory onboarding; the reporting and
verification paths do not depend on it. Fatal errors can still abort that mode.
A `keep-going` snapshot with no recovered errors retains quality `unverified`.
Neither quality label means that a claim has been proved.

Capture stdout and stderr separately, retaining the nonzero exit status:

```sh
skjs check --emit-skjs-type-claims input.ts > claims.json 2> diagnostics.txt
# A nonzero status is expected for a rejected program; inspect it before proceeding.
node verification/tools/annotate-source.mts input.ts --claims claims.json \
  --diagnostics diagnostics.txt --out partial.annotated.ts \
  --verify verification/lean/.lake/build/bin/verifier
```

`--diagnostics` preserves the exact producer diagnostic text in the manifest,
with its path and fingerprint. Diagnostics and collection metadata never become
proof assumptions. The manifest’s `gaps` array makes missing information visible
alongside the available claims. A partial snapshot may fail verification while
an independently complete function in the same supported file verifies.

To experiment with repair, edit a **copy of the raw claims JSON** and rerun
verification against the unchanged source. Missing or incorrect required claims
still fail the independent checker. An actual source type error cannot be made
sound by changing its claims. Report comments are display-only; editing those
comments does not supply evidence. Source edits require fresh spans and claims.

## Reviewing a repair against a baseline

Keep the original report and edit a separate copy of its **input claims**, then
pass the original report's JSON manifest as `--baseline`:

```sh
node verification/tools/annotate-source.mts input.ts --claims repaired-claims.json \
  --producer manual-repair --baseline partial.annotated.ts.json \
  --verify verification/lean/.lake/build/bin/verifier --out repaired.annotated.ts
```

The new annotated copy marks added, changed and removed claim sites. Its manifest
contains `comparison.changes`, with the before/after candidate values, function
identity and original source span. This compares signatures, entry environments
and expression types; collection metadata and saved verification results do not
count as claim changes. Entry binding order and JSON object property order are
immaterial. Raw type payloads are compared when available, otherwise display
strings are compared. This is a structural comparison, not semantic type equality.

Both reports must attach to the same source identity and exact source bytes.
The baseline manifest's digest is retained and checked by `--check-fresh`.
Producer names remain descriptive provenance. Neither that digest nor the
comparison authenticates the baseline or turns its stored results into evidence.
`--verify` freshly produces and independently checks the current claims;
omitting it still produces a claims-only comparison. An empty comparison never
implies that the function is verified.

The regression suite removes a required entry claim from a valid function,
checks failure, restores the original claim, then checks success. It also inserts
a fake saved success into the baseline and confirms that a still-incomplete
candidate continues to fail. This exercises repair of missing information,
without claiming that erroneous source can be repaired by false annotations.

## Calculus-label claim inputs

`--format source-claims` accepts the strict bounded
[producer-independent sidecar](SOURCE-CLAIMS.md), including fresh verification and
baseline comparison. Unlike `--format report`, this is an input to the Lean
consumer, with its own versioned schema and source fingerprint.


For converted SKJS sidecars, `--conversion claims.json.conversion.json` attaches
original collection and recovery labels, diagnostic text and conversion omissions
to the report manifest. It is restricted to `--format source-claims` and to the
exact original sidecar and source snapshot. The renderer bases visitation gaps
on the original export, so a type omitted by conversion is not called an
unfinished expression. All verification results are still obtained freshly
from the current sidecar, never from the conversion manifest.

After editing claims, use the initial report as `--baseline` instead of attaching
the old conversion manifest. `--check-fresh` detects changes to an attached
conversion manifest as well as the report's other inputs.
