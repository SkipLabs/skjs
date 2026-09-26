# Producer-independent source sidecars

The sidecar supplies ground types as calculus labels into a type table the
document carries, and type parameters as function-scoped references. It contains no SKJS type atoms, inferred bounds or stored
proof results. A human or another producer can write it. This is a bounded
interface for the existing source fragment, not support for arbitrary graphs,
TypeScript types, shadowing or recursive source aliases.

```sh
node verification/tools/fragment-parse.mts input.ts > ast.json
verification/lean/.lake/build/bin/verifier --produce-source-claims \
  ast.json source-claims.json input.ts evidence.json 10
verification/lean/.lake/build/bin/verifier --check-source-claims \
  ast.json source-claims.json input.ts evidence.json
```

The consumer reconstructs the calculus requests and required claim obligations
from the AST and sidecar. It checks evidence using the same `checkRequests`
function and soundness theorems as SKJS-backed source checking.
`SourceClaimJson.checkJson_safe` states that every accepted plan first becomes
a `CertifiedPlan` and that every such function has the calculus safety
guarantee, at every assignment of its parameter rows. No SKJS invocation
or `--keep-going` is needed.

Generic functions use the same sidecar: any `type` or `result` may be
`{"param":"T"}`, referring to that function's source type parameter, which
Lean reads as the binder's parameter row (a bounded one as its meet with the
bound) before the unit is extracted as an ordinary graph request, certified at
every assignment of those rows. The TS exporter matches compiler symbol
identities before emitting this name. Bounds come from the source, never from
producer assertions. Ground functions cannot use parameter claims,
and parameter claims cannot carry current-content assertions. Within this fragment,
ground annotations retain their ordinary graph meanings; no parameter is
replaced by its bound. Declarations certify invocation as well as body safety,
and every supplied callee and operand claim is checked at its source span.

## Quantified callables and their eliminations

A `type` may also be `{"scheme":{"typeParams":[...],"this":...,"params":[...],"rest":null,"result":...}}`:
a callable quantified over its own binders, which a binding can hold. Binders
shadow, so a nested scheme's own names hide an outer substitution. `this` is
required: the receiver a call must pass, top for an arrow, and for an ordinary
function its `this` annotation, which may be a binder, so that each call's
receiver instantiates it. `rest` is required: `null` for a fixed signature,
otherwise the type of each surplus actual. A mutable array over a binder is `{"array":{"param":"T"}}`;
its store contract is invariant. After substitution it is interned through the
same list-store and object graph rows as every ordinary array.

An expression that calls one carries the elimination it proposes:

```json
{
  "pos": [121, 129],
  "type": [1, 2],
  "current": null,
  "instantiate": [{ "name": "T", "type": [1, 2] }]
}
```

`instantiate` is absent, or `null`, at every other site. Its names must be
exactly the scheme's binders, and each type argument must be a ground type: an
unresolved parameter or a nested scheme is refused. The consumer re-checks the
substitution and derives the call's arrow from the scheme's own signature, so a
forged `instantiate` can only name another genuine instance.

Lean reads each such scheme as a scheme row whose binders are fresh parameter
rows ([quantified schemes](POSITIVE-TYPES.md#quantified-scheme-layer)): every
claim and annotation inside the closure reads the closure's binders as those
rows, a bounded one as the meet of its row and its bound, one bounded by
another of the closure's binders as the meet of the two parameter rows. The
closure is graph code at the row (`funScheme`), checked once at the row's
signatures, so at every instantiation and never at the observed calls alone: a
closure that satisfies each observed call but cannot produce an arbitrary
binder's value fails its own code's check, whatever its calls. A call of a
local holding one is claimed at the instance its `instantiate` names, a bounded
binder's instance the meet of its type argument with the bound, and the callee
is read there, below the scheme by a checked instance table (`Sub.inst`).
Nested generic closures, generic closures in generic bodies, rests, defaults
and receivers over a binder are all graph code the same way.

Both producers feed this format into `SourceClaimJson`. The native SKJS CLI
entry points first run `SourceClaimExport`; they do not have another verifier.
The viewer collects and edits this format for both producers. Original native
claims are retained only as import provenance or accepted by legacy import tools.
When source parsing is outside the fragment, import still permits inspection in
this format, but verification requires the real source parser and stays unavailable.

## Encoding

An optional function-level `arrows` field supplies per-signature interior claims
for overloaded closures: `[{pos, rows: [{expressions, entries}]}]`. Each row uses
the same expression and entry encodings as the enclosing function. The consumer
checks the body separately for every advertised signature; rows are producer
claims, not evidence of acceptance. Owners must be distinct source closures;
row sites must lie inside their owner, with no duplicate sites, invalid labels,
or unchecked substitutions. Row-specific current-content assertions replace the
whole assertion at that site, including its absence; they are never discarded
or combined with another signature's refinement.

Every field shown below is required. Unknown fields, including stored verification
statuses, are rejected. This illustrative document must be given the actual file
identity, SHA-256 digest and UTF-16 source positions before use:

```json
{
  "file": "input.ts",
  "sourceSha256": "REPLACE_WITH_SHA256_OF_EXACT_SOURCE_BYTES",
  "types": [
    ["nul"],
    [{ "boolLit": { "value": true } }],
    [{ "boolLit": { "value": false } }],
    ["undef"]
  ],
  "functions": [
    {
      "name": "identity",
      "namePos": [9, 17],
      "params": [{ "name": "flag", "type": [1, 2], "current": null }],
      "result": [1, 2],
      "entries": [
        {
          "start": 43,
          "bindings": [{ "name": "flag", "type": [1, 2], "current": null }]
        }
      ],
      "expressions": [{ "pos": [50, 54], "type": [1, 2], "current": null }]
    }
  ]
}
```

A decoder requires every field above and refuses any field not above, so a
document that does not have exactly this shape is rejected rather than read
under some other reading. Every point carries an explicit `current` field.
When the shape changes, regenerate the documents that carry it.

A source with top-level code (module constants and expression statements)
has one more code unit, its module initialization, whose claims are an
`"init"` object beside `"functions"`: `{"entries": [...], "expressions":
[...]}`, with optional `"arrows"`, exactly as a function states them. It is
present exactly when the source has that code. The unit has no parameters and
completes with `undefined`; its sites are the top-level statements. A function
reads the module's functions and annotated constants at their source types,
which no claim states, and an unannotated constant at the `"init"` claim for
its initializer's expression, which the initialization unit checks. See
[Modules and code units](DESIGN.md#modules-and-code-units).

A document whose types use a generic declaration's application has one more
field, `"applications"`: `[{"row": r, "declaration": d, "args": [[...], ...]}]`,
left out when there are none. Row `r` is an empty row the producer reserved;
`d` is the declaration's position among the declaration document's
`definitions`, and `args` its argument types, which name only earlier rows.
Lean fills each such row from the declaration's source terms, in row order,
exactly as it fills a nullary declaration's reserved row, so every declaration
has one lowering, Lean's, whatever producer names it.

Array types are reserved the same way, in `"arrays"`:
`[{"row": r, "store": s, "readonly": b}]`, left out when there are none. Row
`r` is an empty row the producer reserved and `s` the row of the store's tuple
contract, which the producer states. Lean fills the row with the one array
shape (`PositiveNormalization.arrayClauseOf`): the store, `Array.prototype` as
a view at `ArrayProto`, and the own-key bound excluding `ArrayProto`'s keys.
No producer spells that shape.

Intersections are reserved the same way, in `"meets"`:
`[{"row": r, "parts": [[...], ...]}]`, left out when there are none. Row `r`
is an empty row the producer reserved and `parts` its operands' types, which
name only earlier rows. Lean fills the row with their meet as the source's own
`A & B` lowers (`DeclarationGraph.meetRow`), in row order with the
applications: `values.getUnique()` at `Values<[number, number]>` is
`[number, number] & DepSafe`, a row no producer spells. An operand holding a
type parameter is refused there; the producer proposes such an intersection
as its parameter, which Lean's reading of the declaration decides.

Function identity is its name and name span. Parameter names and order must match
the source signature. Entry claims use statement start offsets, and expression
claims use complete spans. Sites must occur in the named function's decoded
body, including loop heads and supported closure bodies. A loop-head entry is
the invariant candidate checked on initial entry and every back edge. The existing extractor resolves names
against initialized lexical bindings and retains its shadowing restrictions.
A `this` binding in an entry is ignored: a receiver is immutable and bound by
the call, so it keeps the type its function's receiver gives it, and a `this`
expression is an ordinary expression site claimed like a variable.
Declaration IDs are not part of this interface.

Type references are sorted, duplicate-free lists of labels into the document's
`types` table, read as a union: `[]` denotes `never`, `[1,2]` denotes `boolean`,
and `[0,1,2]` denotes `null | boolean`. The source decoder also accepts unions
mixing supported cell and function atoms with primitives. Existing limits on
external cell parameters and nested record operands remain in force; fields
and arrow operands admit bounded primitive/callable contracts, and an arrow parameter is assumed at its annotation.

A zero-argument source arrow has an empty domain list `[]`; a unary
`undefined` parameter has domain list `[[3]]`. Arity is retained in both
the source AST and the graph; see [the callable protocol](REQUEST-PROTOCOL.md#expression-closures-and-calls).

The table is the graph the functions are checked against. Row `i` is the list
of clauses that label `i` denotes, and a clause names its operands as label
lists into the same table:

| Row                | Clause                                                         | Meaning                                                                                                                                                                                                                            |
| ------------------ | -------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `0`, `1`, `2`, `3` | `"nul"`, `boolLit true`, `boolLit false`, `"undef"`            | The primitives, fixed                                                                                                                                                                                                              |
| any                | `{"refs": {"first": [["value", A]], "rest": [], "views": []}}` | A plain record with an invariant `value` field holding the union `A`                                                                                                                                                               |
| any                | `{"refs": {"first": F, "rest": [H, ...], "views": V}}`         | One record under every listed field contract; `F`, `H` and `V` are lists of `[name, labels]` pairs. `V` names readonly views: fields read at a sound upper bound on their contents, with no write permission through this contract |
| any                | `{"arrs": {"arrows": [[T, [D, R]]]}}`                          | A signature with receiver union `T`, ordered domain list `D` and result union `R`; a signature indifferent to its receiver names a `"top"` row                                                                                     |

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

On a function atom, `(D1 => R1) & (D2 => R2)`: one function meeting every
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
requires a single record or arrow contract.

A record contract names one location per field, so a claim about what a point
currently holds names the field it is about: `current` is a list of `[field,
labels]` pairs, or `null` where no such assertion is made. A point whose type
names no record cannot carry one.

All labels are validated, including those in unused candidates. Duplicate sites,
bindings and function identities are rejected. All source functions must have
matching claim records. Missing required claims fail extraction or checking;
unrelated bindings at a valid environment site remain subject to the existing
export policy and need not be consumed. A successful function result establishes
the modeled obligations, not every candidate in its environment. This sidecar
therefore does not yet implement the proposed comment frontend's stricter
requirement to consume every directive.

## Arrays

An array claim is one atom:

```json
{ "a": "array", "required": [T, ...], "optional": [T, ...], "rest": T | null, "readonly": false }
```

`number[]` has no required or optional positions and `number` as its rest;
`[number, string]` has two required positions and no rest; `readonly` marks a
`ReadonlyArray` or readonly tuple. The exporter lowers the atom to a record
whose one field, the store, holds a `list` clause with the same positions,
invariantly for a mutable array and as a view for a readonly one, so an array
is an object and its contract is on the store: aliases share it, a write
keeps it. A readonly store contract uses an upper bound at each element location, so element types are covariant; the store-field view grants no replacement permission. Presence of a position
is kept apart from a present `undefined`: an optional or rest position reads
at its type or `undefined`, a required one at its type alone. Optional tuple
positions are not produced by SKJS; the atom carries them for tsc.

The editor prints homogeneous arrays as `Array<T>` or `ReadonlyArray<T>` and
also accepts `T[]` and `readonly T[]`. Tuples use `[T, U?, ...Array<V>]`.
`Store<...>` names the internal store contract when a graph row is edited
by itself; it uses the same structural fields with atom tag `store`. Normalized
array objects lift back to the array spelling. The `readonly` flag on a native
`list` tuple is required, and does not mean the backing locations are immutable.

Source numeric element operations require a valid array-index singleton.
Arbitrary numbers can name ordinary properties (negative, fractional, NaN,
or out of range), which this store does not represent. Destructuring reads
positions of an array, under the trust the array iterator's `%Iterate%`
states; an array pattern's rest is a fresh array, a site claimed like an array
literal at the rest's span (`...r`), and the pattern's reads are not sites. A
slice rest's claim there carries the instance of its `%RestFrom:k%` call,
like a generic call's.

## Current-content assertions

The [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) defines the
combined notation; this section specifies its sidecar encoding.

Bindings and expressions have a required `current` field: `null` means no
additional assertion; otherwise it is a nonempty list of distinct `[field, labels]` pairs. Each field
must belong to the point's record contract; `type` must name exactly one
single-contract plain reference row. Each label list is sorted and
duplicate-free; extraction requires it to denote a finite primitive predicate
(`0` null, `1` true, `2` false, `3` undefined). For example, in a
document whose row 4 is `Ref<boolean>`:

```json
{ "name": "cell", "type": [4], "current": [["value", [1]]] }
```

This displays as `{ value: boolean = (true) }`. The storage invariant and current
predicate are distinct; their [semantic meaning](SEMANTICS.md#current-content-assertions-and-postconditions)
is not a persistent read/write capability. An empty field predicate, `[["value",[]]]`, denotes impossibility, not
absence. The outer `current` array must be nonempty. Function parameters require `current: null`;
ordinary arrows do not acquire creation-time heap assumptions or postconditions.
Numbers, nested predicates, and correlated unions of differently refined
references remain outside this profile.

`Fragment.translatePoint` preserves a supported standalone record refinement
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

An unavailable type is represented as `{"unavailable":"decoder reason"}` at its
original signature, binding or expression site. It never denotes a type, and
using it in an obligation rejects. The native payload and reason also remain in
the import metadata. Entries and expressions absent from the lowered source are
recorded as omissions. These include raw export
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
unfinished expressions from unavailable claims and native sites omitted by conversion. The conversion
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
