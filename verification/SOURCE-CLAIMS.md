# Producer-independent source sidecars

The `stateful-source-v3` profile supplies types directly as calculus labels into
a type table the document carries. It contains no SKJS type atoms, inferred
bounds or stored proof results. A human or another producer can write it. This is a bounded
interface for the existing source fragment, not support for arbitrary graphs,
TypeScript types, shadowing or recursive source aliases.

```sh
node verification/tools/parse-source.mts input.ts > ast.json
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
  "version": 3,
  "profile": "stateful-source-v3",
  "file": "input.ts",
  "sourceSha256": "REPLACE_WITH_SHA256_OF_EXACT_SOURCE_BYTES",
  "types": [["nul"], [{"boolLit": {"value": true}}], [{"boolLit": {"value": false}}], ["undef"]],
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

`stateful-source-v3` is the only accepted profile. Every point carries an
explicit `current` field. Documents written for an earlier profile, including
the fixed-table `stateful-source-532-v2`, are rejected and must be regenerated
rather than upgraded in place.

Function identity is its name and name span. Parameter names and order must match
the source signature. Entry claims use statement start offsets, and expression
claims use complete spans. Sites must occur in the named function's decoded
body, including loop heads and supported closure bodies. A loop-head entry is
the invariant candidate checked on initial entry and every back edge. The existing extractor resolves names
against initialized lexical bindings and retains its shadowing restrictions.
This version does not yet introduce declaration IDs.

Type references are sorted, duplicate-free lists of labels into the document's
`types` table, read as a union: `[]` denotes `never`, `[1,2]` denotes `boolean`,
and `[0,1,2]` denotes `null | boolean`. The source decoder also accepts unions
mixing supported cell and function atoms with primitives. Existing limits on
external cell parameters, primitive field contracts and primitive arrow inputs
and results remain in force; an arrow parameter is assumed at its annotation.

The table is the graph the functions are checked against. Row `i` is the list
of clauses that label `i` denotes, and a clause names its operands as label
lists into the same table:

| Row | Clause | Meaning |
| --- | --- | --- |
| `0`, `1`, `2`, `3` | `"nul"`, `boolLit true`, `boolLit false`, `"undef"` | The primitives, fixed |
| any | `{"refs": {"first": A, "rest": []}}` | `Ref<A>`, an invariant plain cell holding the union `A` |
| any | `{"refs": {"first": A, "rest": [B, ...]}}` | One location under every listed contract, `Ref<A> & Ref<B>` |
| any | `{"arrs": {"arrows": [[D, R]]}}` | The unary arrow `D => R` |

The table starts with the four primitives and holds one further row per compound
type the source mentions, in order of first use: a compound type gets a row the
first time it is translated and the same label afterwards, so equal types share
a label and no row exists that nothing uses. Labels are names, not meanings:
`[4]` is `Ref<boolean>` in a document whose row 4 says so, and the checker's
theorems hold for every table (`HasTy.sound` is graph-generic). Any table that
starts with the primitives and refers only to its own labels is accepted;
`SourceTypes.label_meaning` proves that a labelled clause means exactly that
clause. The exporter writes the table it built, and `--produce` may grow a
request's table further with annotations the claims did not mention.

## Conjunction

An atom list is a union: its members are alternatives. Conjunction is not
written there, because it is not a union of anything. It is written inside the
atom kinds that have one, which is where the clause language puts it: `refs`
carries a first contract and the rest, `arrs` carries a list of signatures, and
`nul`, `bool`, `boolLit` and `undef` carry nothing. So an atom may carry `and`,
a list of further atoms of the same kind:

```json
{ "a": "record", "fields": [ ... ], "and": [ { "a": "record", "fields": [ ... ] } ] }
```

which is `Ref<A> & Ref<B>`: one location meeting both contracts invariantly. An
absent or empty `and` is the ordinary single-contract atom, unchanged.

or, on a function atom, `(D1 => R1) & (D2 => R2)`: one function meeting every
signature. The rule that keeps this honest is that the format may not be able
to say more than the clause language can hold. `and` on a primitive atom is
refused, because no clause conjoins primitives and a decoder would have to
invent a meaning for it. Conjunction is associative, so the parser flattens a
parenthesized intersection into the same list; there is no arity.

A conjunction of references lowers to one `refs` row. It is commutative and
idempotent, so the operands are sorted and deduplicated before the row is
interned: the two spellings of a pair share a label, and a conjunction of one
contract is the plain cell. A conjunction of arrows lowers to one `arrs` row
with the signatures in declaration order, which is TypeScript's overload
resolution order; only exact repeats are dropped, so the two spellings are two
rows that mean the same set.

The lambda rule proves a body once under each claimed signature, and a call
resolves to the first signature whose parameter admits the argument's claimed
type, as TypeScript does. Each claimed parameter must lie within the lambda's
annotated one, so no signature leaves the source's declared domain. Expression
claims inside the body are one type per site, holding under every signature,
so a body whose result depends on the signature cannot yet be claimed
per signature.

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
labels (`0` null, `1` true, `2` false, `3` undefined). With a non-null assertion,
`type` must be exactly one single-contract reference label. For example, in a
document whose row 4 is `Ref<boolean>`:

```json
{"name":"cell","type":[4],"current":[1]}
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
Every statement entry resets to exactly its supplied types and current predicates;
extra derived facts and links cannot cross it. All incoming edges must justify
that interface, including loop backedges. Expression claims are local obligations
within a statement, where checked effects may preserve or derive facts. The
source consumer enforces both policies independently of evidence production.

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
node verification/tools/annotate-source.mts input.ts \
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
node verification/tools/export-source-claims.mts input.ts --claims skjs-claims.json \
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
node verification/tools/annotate-source.mts input.ts --format source-claims \
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
