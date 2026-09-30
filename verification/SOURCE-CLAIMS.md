# Producer-independent source sidecars

The sidecar supplies ground types as calculus labels into a type table the
document carries, and type parameters as function-scoped references. It contains no inferred bounds or stored
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
from the AST and sidecar. It checks evidence using `checkRequests` and its soundness theorems.
`SourceClaimJson.checkJson_safe` states that every accepted plan first becomes
a `CertifiedPlan` and that every such function has the calculus safety
guarantee, at every assignment of its parameter rows.

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

A `type` may also be `{"scheme":{"typeParams":[...],"this":...,"params":[...],"rest":null,"result":...,"effect":"unrestricted"}}`:
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

The required `effect` is either `unrestricted` or `preservesInputHeap`, as in
ordinary graph signatures. Grounding a symbolic claim, substitution and scheme
instantiation retain it; definition certification checks it. Source annotations
remain unrestricted. OCaml currently infers preservation for operationally pure
closure bodies and defaults; its analysis is deliberately incomplete for reads,
allocation, calls and rest-array wrappers. Those bodies retain unrestricted
claims until the compositional checker can certify their stronger effect.

Lean reads each such scheme as a scheme head of its own, whose binders are
its application's owned parameters
([RECURSIVE-EQUATIONS §5](RECURSIVE-EQUATIONS.md#5-from-source)): every claim
and annotation inside the closure reads the closure's binders, spelled by
their names, as those parameters, a bounded one as the meet of its parameter
and its bound, one bounded by another of the closure's binders as the meet of
the two parameters. The
closure is graph code at the row (`funScheme`), checked once at the row's
signatures, so at every instantiation and never at the observed calls alone: a
closure that satisfies each observed call but cannot produce an arbitrary
binder's value fails its own code's check, whatever its calls. A call of a
local holding one is claimed at the instance its `instantiate` names, a bounded
binder's instance the meet of its type argument with the bound, and the callee
is read there, below the scheme by a checked instance table (`InstArrs`).
Nested generic closures, generic closures in generic bodies, rests, defaults
and receivers over a binder are all graph code the same way.

Both producers feed this format into [SourceClaimJson.lean](lean/Verification/Model/Source/SourceClaimJson.lean), its strict decoder and checked consumer.
The viewer collects and edits this format for both producers.

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

Type references are lists of labels, read as a union: `[]` denotes `never`,
`[1,2]` denotes `boolean`, and `[0,1,2]` denotes `null | boolean`. A label is
a row of the document's `types` table, or a tree naming a type whose row only
the verifier builds, from the declaration document the parser emits:

| Label | Spelling | Denotes |
| --- | --- | --- |
| row | `i` | the clauses of row `i` of `types`, each spelled as [the request fields](REQUEST-PROTOCOL.md#request-fields) give it |
| application | `{"decl": k, "args": [A, ...]}` | declaration `k`, its position in the declaration document's `definitions`, applied to one union per parameter, an omitted argument written as its default at the earlier arguments; `args` is left out for a nullary declaration, and never written empty |
| intersection | `{"meet": [A, ...]}` | the intersection of at least two unions, as the source's own `A & B` lowers (`EquationLowering.meetOf`) |
| array | `{"array": [s], "readonly": b}` | the array whose store has the tuple contract of row `s`, with `Array.prototype` as a view at `ArrayProto` and the own-key bound excluding `ArrayProto`'s keys (`PositiveNormalization.arrayClauseOf`) |
| binder | `{"binder": "T"}` | the binder `T` in scope, as its unit, closure or class's generic method binds it, a bounded one within its bound: the label alone states the bound, which a claim does not restate |

```math
\begin{aligned}
L &::= i \;\mid\; \mathsf{decl}(k, A_1, \ldots, A_n) \;\mid\; \mathsf{meet}(A_1, \ldots, A_m) \;\mid\; \mathsf{array}(s, b) \;\mid\; \mathsf{binder}(T)
\qquad n = \mathrm{arity}(k),\ m \ge 2\\
A &::= [L_1, \ldots, L_p] \qquad L_1 < \cdots < L_p
\end{aligned}
```

A label list is in canonical order, each label once: rows ascending, then
applications, intersections, arrays and binders, each ordered by its fields in
turn, lists lexicographically with a prefix first. Each tree has this one
spelling and no other field. So a producer never writes a declaration's
equation, an array's shape, an intersection's row or a binder's row: its
`types` are the four primitives, then its own clause rows and the scheme rows
of classes' generic methods, whose binders are binder labels. The verifier
lowers the claims with the source's declarations to recursive equations
([RECURSIVE-EQUATIONS §5](RECURSIVE-EQUATIONS.md#5-from-source)):
a row is a head of its own, lifted over the binder names it mentions, and a
binder label is its name, read as the unit or closure that binds it gives
it. The
source decoder also accepts unions
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
starts with the primitives and refers only to its own labels is accepted, and
Lean reads its rows as heads of the equations the checked requests are over
([lowering](RECURSIVE-EQUATIONS.md#5-from-source)). The exporter writes the table it built, and `--produce` may grow a
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
{ "a": "array", "required": [T, ...], "optional": [T, ...], "rest": T | null, "readonly": false, "dense": true }
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
positions are carried for tsc.
The required `dense` flag excludes holes below the length when true; when
false, required positions remain present but optional/rest entries may be
holes. Source arrays currently request density; native `map` results do not.

The editor prints homogeneous arrays as `Array<T>` or `ReadonlyArray<T>` and
also accepts `T[]` and `readonly T[]`. Tuples use `[T, U?, ...Array<V>]`. The prefix `sparse` states
`dense: false`, for example `sparse ReadonlyArray<number>` or
`sparse [number, string?]`; it composes with `Store<...>`.
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
duplicate-free; extraction reads it as a finite primitive predicate
(`0` null, `1` true, `2` false, `3` undefined), or, for a field of an
immutable binding's object, a type none of whose values is `undefined` as the
predicate `defined`; any other label list the field's contract must imply. For example, in a
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

A supported standalone record refinement is its write-invariant reference plus
its read-content predicate. The sidecar consumer binds current predicates to statement-entry or expression-result graph checkpoints.
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

Before ordinary invariant-cell translation, `translate` in [CellUnion.lean](lean/Verification/Model/Types/CellUnion.lean) validates every
record alternative. It may absorb an arm only into an existing invariant arm,
with a weaker read requirement and **the same** write invariant. Writing `C(R,W)`
for the schema's read/write requirements, the sufficient rule is:

```math
\frac{R_1 \subseteq R_2 \qquad W_1 = W_2}
     {C(R_1,W_1) \preceq C(R_2,W_2)},
\qquad
C(R_1,W) \lor C(R_2,W) \equiv C(R_2,W).
```

The equality uses the premise on the left. `covers_sound` and `normalize_exact`
prove the implication and union preservation for the capability schema. This is
an input-normalization law, not a new declarative program-typing rule. All surviving ordinary arms must have equal read/write
meanings; malformed or unsupported arms are never dropped.

Different write invariants must not be absorbed: a Boolean-world cell currently
true need not be `Ref true`. Thus `C(true,boolean) | C(true,true)` cannot become
`C(true,true)` under the point interpretation. `observed_union_absorb` separately
proves observation absorption at a fixed invariant. The corresponding model
counterexample is `observation_does_not_narrow_invariant` in `ModelBoundaries.lean`.

## Source identity and trust

The external parser now includes `sourceSha256` in its AST output. The sidecar's
file identity and digest must match that AST. The report command additionally
checks the digest against the actual source text. Hashing and parsing remain
part of the reviewed source boundary; Lean checks agreement of the supplied
identities, not a theorem that the JSON AST describes those source bytes.
Editing source requires regenerating the AST and updating claim positions and
fingerprint. Supplying evidence from a previous judgment cannot bypass checking.

## Reports

The report command accepts this format:

```sh
node verification/tools/annotate-source.mts input.ts \
  --format source-claims --producer manual --claims source-claims.json \
  --verify verification/lean/.lake/build/bin/verifier --out input.annotated.ts
```

Producer names are display provenance;
they are not sidecar proof assumptions. Claims-only reports are displays, not
schema certification: `--verify` invokes the authoritative strict Lean decoder.

The generic `--format report` is a separate display-only format.
