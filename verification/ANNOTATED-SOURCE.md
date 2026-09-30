# Annotated source reports

[`tools/annotate-source.mts`](tools/annotate-source.mts) writes a separate TypeScript copy showing producer
claims, optionally with freshly checked function results. It also writes a JSON
manifest preserving the claims, diagnostics and content fingerprints. Producer
names are reported provenance, not authenticated identities. The original source and claim files are not modified. Existing output files are
never overwritten.

```sh
node verification/tools/annotate-source.mts input.ts \
  --claims source-claims.json --producer ocaml \
  --verify verification/lean/.lake/build/bin/verifier
```

The default outputs are `input.annotated.ts` and `input.annotated.ts.json`.
`--out /path/report.ts` chooses another destination. The claims file is a
[source-claims](SOURCE-CLAIMS.md) document (`--format source-claims`, the
default). `--file-key` selects its file key if that differs from the input
path. The command does not rerun the producer or alter its claims. Omit `--verify` to generate a claims-only report; use `--depth N` to
set proof-search depth (default 10).

A typical excerpt looks like:

```ts
/* @verify-report kind=function; id=f0; function copyTrue; producer=ocaml; claimed () => boolean; verification=verified */
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
| `reason` | gaps | Why nothing is claimed here, as a stable slug: `statement-not-visited`, `expression-without-type`, `claims-unavailable`. |
| `unsupported` | entries | Bindings in that environment whose exported payload could not be decoded, joined by `+`. |

Manifest records carry the same `id`, so a tool can display a mark and look up
its exact producer payload without matching on positions or prose.

Types use the self-contained [viewer language](VIEWER-LANGUAGE.md): primitive
names, literals, unions, records with optional fields, function signatures, and
callable objects. `{ value: boolean = (true) }` states both a storage invariant
and current contents. Nondefault object modes appear explicitly after `@`.
`tools/claim-text.mts` prints this language for reports and the reader;
`tools/claim.mts` declares and validates its types. A claim outside the
language is shown as its exact JSON; it is never approximated into a supported
shape.

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
source extraction stopped before proof checking; it is not a failed claim.

A proof-search failure can additionally include `obligation`, a structured
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

The manifest also exposes `missingFunctions`: source declarations the claims say
nothing about, with `name`, `namePos`, full `pos` and `missingSites`. These are
parser-derived, not inferred types or verified facts. The reader validates their
spans before presenting them.

Manifest functions also expose `missingSites`: parser-identified expression and
statement-entry spans without a claim, each with a `kind` (`expression` or
`environment`) and `syntax` label. These are possible attachment locations, not
a declaration that verification needs a claim at every one; the source adapter
and verifier decide which claims are required.

Manifest functions include a `pos: [start, end]` range for the full source function,
using original UTF-16 offsets. A reader can therefore focus a function without
reconstructing its boundaries from display comments.

`--stdout json` writes `{"annotated": …, "manifest": …}` to standard output and
creates no files, for callers that render a report without keeping one.

## Reading a report

The reader in `report-viewer/` draws each claim as a bracket under the span it
is about, with the bindings an entry carries beside it. It has the same
standing as this format: display only. It reads the structured manifest rather
than these comments — `report-viewer/serve.mts` runs the producer and this
generator on a chosen file, so a report is produced and read in one step. See
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
display format is distinct from the [source-claim sidecar](SOURCE-CLAIMS.md).
It is not a shortcut around normalizing and checking a new producer's types.

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
and compares the original and annotated TypeScript ASTs, including token text
(read as the parser reads it: a template substitution's closing brace resumes
the template). An expression annotation sits at a node, a token, or a partial
concatenation of a template, which the parser writes from the template's start
to the end of one of its parts. Expression annotations introduce no new line breaks, preserving `return` and
other automatic-semicolon behavior. This is a display transformation, not a
proof of the separate source-to-calculus lowering.

## Calculus-label claim inputs

`--format source-claims` accepts the strict bounded
[producer-independent sidecar](SOURCE-CLAIMS.md), including fresh verification.
Unlike `--format report`, this is an input to the Lean
consumer, with its own schema and source fingerprint.
