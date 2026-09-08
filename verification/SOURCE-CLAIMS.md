# Producer-independent source sidecars

The `stateful-source-75-v2` profile supplies types directly from the current
calculus source graph. It contains no SKJS type atoms, inferred bounds or stored
proof results. A human or another producer can write it. This is a bounded
interface for the existing source fragment, not support for arbitrary graphs,
TypeScript types, shadowing or recursive source aliases.

```sh
node verification/tools/parse-source.js input.ts > ast.json
verification/lean/.lake/build/bin/verifier --produce-source-claims \
  ast.json source-claims.json input.ts evidence.json 10
verification/lean/.lake/build/bin/verifier --check-source-claims \
  ast.json source-claims.json input.ts evidence.json
```

The consumer reconstructs the calculus requests and required claim obligations
from the AST and sidecar. It checks evidence using the same `checkRequests`
function and soundness theorems as SKJS-backed source checking.
`SourceClaimJson.checkJson_checked` ties acceptance of this interface to those
checks. No SKJS invocation or `--keep-going` is needed.

## Encoding

Every field shown below is required. Unknown fields, including stored verification
statuses, are rejected. This illustrative document must be given the actual file
identity, SHA-256 digest and UTF-16 source positions before use:

```json
{
  "version": 2,
  "profile": "stateful-source-75-v2",
  "file": "input.ts",
  "sourceSha256": "REPLACE_WITH_SHA256_OF_EXACT_SOURCE_BYTES",
  "functions": [{
    "name": "identity",
    "namePos": [9, 17],
    "params": [{"name": "flag", "type": [1, 2], "current": null}],
    "result": [1, 2],
    "entries": [{
      "start": 43,
      "bindings": [{"name": "flag", "type": [1, 2], "current": null}]
    }],
    "expressions": [{"pos": [50, 54], "type": [1, 2], "current": null}]
  }]
}
```

Version 2 adds an explicit `current` field to bindings and expressions without
changing the 75 type labels. Version-1 (`stateful-source-75-v1`) documents remain
readable in their exact old shape, without that field; adding it to version 1 is
rejected. Older 19-label sidecars must be regenerated.

Function identity is its name and name span. Parameter names and order must match
the source signature. Entry claims use statement start offsets, and expression
claims use complete spans. Sites must occur in the named function's decoded
body, including loop heads and supported closure bodies. A loop-head entry is
the invariant candidate checked on initial entry and every back edge. The existing extractor resolves names
against initialized lexical bindings and retains its shadowing restrictions.
This version does not yet introduce declaration IDs.

Type references are sorted, duplicate-free lists of labels. The list denotes a
union; `[]` denotes `never`, `[1,2]` denotes `boolean`, and `[0,1,2]` denotes
`null | boolean`. The source decoder also accepts unions mixing supported cell
and function atoms with primitives; the profile itself does not change. For
example, `[0,9]` represents a nullable Boolean cell. Existing limits on external
cell/function parameters, primitive field contracts and primitive arrow inputs
and results remain in force. The profile fixes the graph to `SourceTypes.types`:

| Labels | Meaning |
| --- | --- |
| `0`, `1`, `2` | `null`, `true`, `false`, respectively |
| `3 + m`, for `0 ≤ m < 8` | `Ref<U(m)>`, an invariant plain cell contract |
| `11 + 8d + r`, for `0 ≤ d,r < 8` | Unary arrow `U(D[d]) → U(r)`, where `D = [1,0,2,3,4,5,6,7]` |

`U(m)` is the union selected by the mask: bit 0 selects null, bit 1 true, and bit
2 false. Thus label `9` is `Ref<boolean>` and label `17` is `null → boolean`.
These are calculus contracts; the source boundary still checks that allocations
and operations justify their interpretation. An array of several reference or
arrow labels can be decoded, but the source adapter may reject its use where it
requires a single cell or arrow contract.

All labels are validated, including those in unused candidates. Duplicate sites,
bindings and function identities are rejected. All source functions must have
matching claim records. Missing required claims fail extraction or checking;
unrelated bindings at a valid environment site remain subject to the existing
export policy and need not be consumed. A successful function result establishes
the modeled obligations, not every candidate in its environment. This sidecar
therefore does not yet implement the proposed comment frontend's stricter
requirement to consume every directive.

## Current-content assertions

The [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) defines the
combined notation; this section specifies its sidecar encoding.

Bindings and expressions have a required `current` field: `null` means no
additional assertion; otherwise it is a sorted, duplicate-free list of primitive
labels (`0` null, `1` true, `2` false). With a non-null assertion, `type` must be
exactly one invariant-reference label, from 3 through 10. For example:

```json
{"name":"cell","type":[9],"current":[1]}
```

This displays as `{ value: boolean = (true) }`. The storage invariant and current
predicate are distinct; their [semantic meaning](SEMANTICS.md#current-content-assertions-and-postconditions)
is not a persistent read/write capability. An empty `current` array denotes the
empty predicate and is not absence. Function parameters require `current: null`;
ordinary arrows do not acquire creation-time heap assumptions or postconditions.
Numbers, nested predicates, and correlated unions of differently refined
references remain outside this profile.

`SourceInput.translatePoint` preserves a supported standalone record refinement
as its write-invariant reference plus its read-content predicate. Conversion does
not manufacture stronger producer claims. Both raw SKJS and sidecar consumers
bind current predicates to statement-entry or expression-result graph checkpoints.
All incoming edges must justify them, including loop backedges. The source consumer
also checks that the certificate has retained the reconstructed requirements;
changing an assertion invalidates evidence that does not imply it.

Observations inside ordinary closure/compositional proofs require the storage
invariant to imply the predicate uniformly. They do not inherit creation-time
heap facts. [Program typing](PROGRAM-TYPING.md#source-observation-checkpoints)
specifies that conservative obligation. Failure to prove an observation is a
located proof obligation, not an unavailable-type or unsupported-format result.
[Design](DESIGN.md#current-content-assertions) owns remaining precision work.

## Record alternative absorption

Before ordinary invariant-cell translation, `CellUnion.translate` validates every
record alternative. It may absorb an arm only into an existing invariant arm,
with a weaker read requirement and **the same** write invariant. Writing `C(R,W)`
for the schema's read/write requirements, the sufficient rule is:

$$
\frac{R_1 \subseteq R_2 \qquad W_1 = W_2}
     {C(R_1,W_1) \preceq C(R_2,W_2)},
\qquad
C(R_1,W) \lor C(R_2,W) \equiv C(R_2,W).
$$

The equality uses the premise on the left. `covers_sound` and `normalize_exact`
prove the implication and union preservation for the capability schema. This is
an input-normalization law, not a new declarative program-typing rule or a proved
correspondence to SKJS. All surviving ordinary arms must have equal read/write
meanings; malformed or unsupported arms are never dropped.

Different write invariants must not be absorbed: a Boolean-world cell currently
true need not be `Ref true`. Thus `C(true,boolean) | C(true,true)` cannot become
`C(true,true)` under the point interpretation. `observed_union_absorb` separately
proves observation absorption at a fixed invariant. The corresponding model
counterexample and normalizer regression live in `HeapObservationTests.lean`.

## Source identity and trust

The external parser now includes `sourceSha256` in its AST output. The sidecar's
file identity and digest must match that AST. The report command additionally
checks the digest against the actual source text. Hashing and parsing remain
part of the reviewed source boundary; Lean checks agreement of the supplied
identities, not a theorem that the JSON AST describes those source bytes.
Editing source requires regenerating the AST and updating claim positions and
fingerprint. Supplying evidence from a previous judgment cannot bypass checking.

## Reports and repairs

The existing report and comparison command accepts this format:

```sh
node verification/tools/annotate-source.js input.ts \
  --format source-claims --producer manual --claims source-claims.json \
  --verify verification/lean/.lake/build/bin/verifier --out input.annotated.ts
```

After editing a copy of the sidecar, add
`--baseline input.annotated.ts.json` and choose a fresh `--out` path. The report
shows edits and freshly checked results. Producer names are display provenance;
they are not sidecar proof assumptions. Claims-only reports are displays, not
schema certification: `--verify` invokes the authoritative strict Lean decoder.

The generic `--format report` remains a separate display-only format. The new
sidecar is also distinct from SKJS export JSON. The converter below reuses the
existing type decoder; comment editing remains a future step. The regression
suite supplies handwritten
claims for primitive parameters and for a mutable cell captured by a closure,
and checks malformed inputs, missing claims, false refinements and old evidence.

## Converting an existing SKJS export

```sh
node verification/tools/export-source-claims.js input.ts --claims skjs-claims.json \
  --diagnostics diagnostics.txt --out source-claims.json
```

The command uses the current source parser and Lean's existing SKJS type decoder.
It never invokes SKJS or enables recovery. `--diagnostics` is optional; use
`--file-key` if the raw export identifies the file differently from the input
path. `--verifier` selects the executable implementing conversion.

Two files are written, without modifying inputs or overwriting existing outputs:

- `source-claims.json`: editable calculus-label candidates.
- `source-claims.json.conversion.json`: original raw claims, function collection
  metadata, exact optional diagnostics, input/tool fingerprints and all omissions.

Unsupported binding or expression types are omitted with their original payload
and decoder error recorded. An unsupported signature omits that function rather
than inventing parameter or result types. Entries and expressions absent from
the lowered source are also recorded as omissions. These include raw export
sites not used by the source adapter; they do not necessarily indicate errors.
Malformed inputs and duplicate identities are rejected instead of merged.

Conversion can succeed on an aborted first-error snapshot. It preserves the
available candidates and does not fill missing obligations. Independent checking
still rejects missing required claims. The optional `--keep-going` mode belongs
to the original SKJS invocation: recovery metadata survives in the conversion
manifest and never becomes a proof assumption.

Review that manifest alongside the sidecar, particularly for recovered exports.
Attach it explicitly when making the initial report:

```sh
node verification/tools/annotate-source.js input.ts --format source-claims \
  --claims source-claims.json --conversion source-claims.json.conversion.json \
  --verify verification/lean/.lake/build/bin/verifier --out initial.annotated.ts
```

The report shows **original SKJS collection** status and recovery labels,
retains diagnostics and omissions, and uses the original snapshot to distinguish
unfinished expressions from claims omitted by conversion. The conversion
manifest must match both the source identity and the exact sidecar bytes. Its
fingerprint participates in report freshness checks. These are provenance
checks, not authentication or proof of the producer's descriptions.

Keep this initial report as the baseline before editing a copy of the sidecar.
For edited claims, omit `--conversion` and use
`--baseline initial.annotated.ts.json` with fresh verification. An old conversion
manifest is rejected for changed sidecar bytes, even whitespace changes: original
collection labels must not silently describe edited candidates. The baseline
retains the original history while the new report describes current claims.
The initial SKJS export has no source digest, so matching it to the chosen source
snapshot still requires care: conversion checks function/site identities but
cannot detect every stale raw export whose offsets happen to remain valid. The
resulting sidecar is bound to the source snapshot used for conversion.

The exporter is a candidate producer, outside the acceptance foundation. For the
real closure corpus, regression tests check evidence in both directions: evidence
produced from SKJS claims is accepted against converted claims, and evidence from
the converted claims is accepted against the original SKJS input. Other tests
cover normal failure snapshots, explicit recovery, preserved diagnostics and
unsupported types remaining missing obligations.
