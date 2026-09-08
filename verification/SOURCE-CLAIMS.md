# Producer-independent source sidecars

The `stateful-source-19-v1` profile supplies types directly from the current
calculus source graph. It contains no SKJS type atoms, inferred bounds or stored
proof results. A human or another producer can write it. This is a bounded
interface for the existing source fragment, not support for arbitrary graphs,
TypeScript types, shadowing or recursive source aliases.

```sh
node verification/tools/parse-source.js input.ts --stateful > ast.json
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
  "version": 1,
  "profile": "stateful-source-19-v1",
  "file": "input.ts",
  "sourceSha256": "REPLACE_WITH_SHA256_OF_EXACT_SOURCE_BYTES",
  "functions": [{
    "name": "identity",
    "namePos": [9, 17],
    "params": [{"name": "flag", "type": [1, 2]}],
    "result": [1, 2],
    "entries": [{
      "start": 43,
      "bindings": [{"name": "flag", "type": [1, 2]}]
    }],
    "expressions": [{"pos": [50, 54], "type": [1, 2]}]
  }]
}
```

Function identity is its name and name span. Parameter names and order must match
the source signature. Entry claims use statement start offsets, and expression
claims use complete spans. Sites must occur in the named function's decoded
body, including supported closure bodies. The existing extractor resolves names
against initialized lexical bindings and retains its shadowing restrictions.
This version does not yet introduce declaration IDs.

Type references are sorted, duplicate-free lists of labels. The list denotes a
union; `[]` denotes `never`, `[1,2]` denotes `boolean`, and `[0,1,2]` denotes
`null | boolean`. The profile fixes the graph to `SourceTypes.types`:

| Labels | Meaning |
| --- | --- |
| `0`, `1`, `2` | `null`, `true`, `false`, respectively |
| `3 + m`, for `0 ≤ m < 8` | `Ref<U(m)>`, an invariant plain cell contract |
| `11 + m`, for `0 ≤ m < 8` | Unary arrow `null → U(m)` |

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
Sidecar reports do not automatically load conversion provenance; their results
concern the supplied candidates. Keep an initial annotated sidecar report as the
baseline before editing a copy, then verify and compare the edited copy normally.
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
