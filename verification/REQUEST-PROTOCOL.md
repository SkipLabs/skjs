# Stateful calculus request protocol

The verifier accepts a JSON request for the
stateful calculus, separately from its derivation certificate. This is a
consumer boundary for extracted programs. It is **not** a decoder for SKJS's
source-associated claims, and it does not certify TypeScript text by itself.

Raw requests and the source modes below use the same executable and consumer.
This document owns calculus request/evidence formats and SKJS source AST/export
encoding. [SOURCE-CLAIMS](SOURCE-CLAIMS.md) owns independent sidecar schemas,
conversion and repairs; [diagnostics](OBLIGATION-DIAGNOSTICS.md) owns failure metadata.

## Run a request

Build from `verification/lean`:

```sh
lake build
```

Save this minimal request as `request.json`:

```json
{
  "types": [["nul"]],
  "program": [{"expression": "nul", "continuation": "ret"}],
  "claims": [{"context": [], "type": [0]}],
  "result": [0],
  "start": 0,
  "inputs": []
}
```

Then produce evidence and check it independently:

```sh
.lake/build/bin/verifier --produce-stateful request.json evidence.json 12
.lake/build/bin/verifier --check-stateful request.json evidence.json
```

`12` limits expression proof-search depth. It is not an execution budget and
is not part of the request, evidence or safety theorem. Production reports
failure if evidence cannot be found and checked. The checking command never
invokes the producer; exit zero means the submitted certificate passed for the
submitted request. Read, parse, validation, checking and output-write failures
return nonzero.

## Request fields

All fields are explicit; object field order is immaterial.

| Field | Meaning |
| --- | --- |
| `types` | A finite array of normalized type-graph nodes. Its array positions are type labels. |
| `program` | A finite array of calculus nodes. Its positions are control-flow labels. |
| `claims` | One entry context and expression-result type per program node, in the same order. |
| `result` | The required result type of the graph. |
| `start` | The designated control-flow entry label. |
| `inputs` | External argument types in slot order. The designated entry context must equal this contract. Use `[]` for closed invocation. |

A type is a list of type labels, interpreted as their union. The empty list
means bottom. Every label, including labels in unused type definitions and
intermediate certificate types, must index the request's `types` array.
Dangling type labels are rejected instead of acquiring the total Lean graph's
default interpretation. Control-flow target existence and expression scope are
checked by the graph consumer.

Each type-graph node is a union of clauses:

| Clause | JSON example |
| --- | --- |
| Null | `"nul"` |
| Boolean | `"bool"` |
| Boolean singleton | `{"boolLit":{"value":true}}` (or `false`) |
| Invariant reference with optional additional contract requirements | `{"refs":{"first":[["value",[1]]],"rest":[]}}` |
| Intersection of arrows | `{"arrs":{"arrows":[[[[0]],[1]],[[[1]],[0]]]}}` |
| Callable with invariant bag requirements and overloads | `{"callable":{"first":[["value",[1]]],"rest":[],"arrows":[[[[0]],[1]]]}}` |

The arrow example contains two argument-list/result pairs, each with one
argument. Each argument type is itself a list of union labels. References and arrow
operands may point back to the same finite graph, representing guarded regular
recursion. The request already contains normalized clauses: this grammar has no conjunction
above the clause level, so nothing here needs normalizing. A producer that does
hold positive formulas has a
[proved normalization interface](POSITIVE-TYPES.md#recursive-normalization) to
translate them; no current extractor uses it. No string, generic or unsupported-type
fallback is supplied by this protocol. `number` and `numberlit` are carried:
`number` is one clause and each `numberlit` is its own, interned on use rather
than given a fixed row, since the singletons are unbounded. A literal's identity
is the bit pattern of the double it denotes, so distinct spellings of one value
are one clause; two spellings a codec failed to identify would be two
singletons, which costs completeness and never soundness.

Current-content assertions use a finite list of primitive predicates, including
`num` for any numeric value and `numLit` for an exact bit pattern. They are
checked on every incoming edge. Unsupported predicates still require a proof
that the storage contract implies the claim; they are never silently discarded.

## Terms, targets and evidence

The JSON codecs use Lean's tagged constructor encoding: nullary constructors
are strings; other constructors are single-key objects containing named fields.
For example:

```json
{"app":{"f":{"var":{"i":0}},"a":"nul"}}
```

This applies slot zero to null. A mapped bind continuation is:

```json
{"bind":{"next":{"label":3,"mapping":[0,2]}}}
```

Its map acts after pushing the result: target slot zero receives source slot
zero, and target slot one receives source slot two. `"mapping":null` means
identity selection. Missing `mapping` is rejected; the protocol does not silently
supply a default.

The encoding follows mechanically from the
[term grammar](SEMANTICS.md#operational-language) and the
[continuations](PROGRAM-TYPING.md#checked-control-flow-graphs). In full, writing
`t` for a nested term and `T` for a target object:

| Term | JSON | Continuation | JSON |
| --- | --- | --- | --- |
| slot $i$ | `{"var":{"i":0}}` | `ret` | `"ret"` |
| $\mathsf{let}(t,t)$ | `{"letE":{"a":t,"b":t}}` | `bind` | `{"bind":{"next":T}}` |
| $\mathsf{call}(t,[t,\ldots])$ | `{"call":{"f":t,"args":[t]}}` | `effect` | `{"effect":{"next":T}}` |
| null, undefined, true, false | `"nul"`, `"undef"`, `"tru"`, `"fls"` | `branch` | `{"branch":{"yes":T,"no":T}}` |
| object with named locations | `{"objAt":{"fields":[["value",0]],"call":c}}` | `branchBind` | `{"branchBind":{"yes":T,"no":T}}` |
| allocation with ordered initializers | `{"makeAt":{"call":c,"names":["value"],"inits":[t]}}` | `tagBind` | `{"tagBind":{"test":"isNul","yes":T,"no":T}}` |
| field read | `{"readAt":{"field":"value","a":t}}` | | |
| field write | `{"writeAt":{"field":"value","a":t,"b":t}}` | | |
| $\mathsf{test}_k(t)$ | `{"test":{"k":"isNul","a":t}}` | | |
| $\mathsf{if}\;t\;t\;t$ | `{"ite":{"c":t,"t":t,"e":t}}` | | |

A descriptor `c` is `"absent"` or `{"closure":{"arity":2,"body":t}}`. Plain allocation
uses the absent descriptor; function creation uses a closure descriptor and an
ordered field initializers. The body is under `arity` parameter binders, in declaration
order, before any captures. Creation evidence requires each overload to have
that many argument types. Application evidence carries every actual argument in order. Runtime object terms
are rejected in supplied graph syntax, including inside unused branches and
closure bodies.

Tests are `isNul`, `isUndef`, `isNullish`, `isBool`, `isRef` and `isFun`.
`isNullish` accepts null and undefined; false takes its negative branch. A location never appears
in a supplied program: it arises only during execution. These are Lean's derived
codecs, so the field names are the constructor's own; they live in
[RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean).

The evidence file is an object with one field, `certificate`, a list of
`NodeEvidence` objects. Each node supplies its expression derivation tree and
one subtype-evidence list per outgoing edge. A derivation node names the
[typing rule](PROGRAM-TYPING.md#judgments-and-constructor-views) it applies:
`var`, `nul`, `undef`, `tru`, `fls`, `truLit`, `flsLit`, `numLit`, `num`,
`funE`, `app`, `letE`, `alloc`,
`read`, `write`, `ifBool`, `ifTrue`, `ifFalse`, `ifKnown`, `ifBoolVar`,
`unionVar`, `makeCallable`, `callCallable`, `readCallable`, `writeCallable`, or `sub`. `ifTrue` and `ifFalse` are the two answers of the single
shape-test rule `ifTag`, split so that the evidence records which answer it
relies on; `truLit` and `flsLit` are the Boolean singleton introductions, and
`numLit` and `num` the numeric ones, a literal at its own singleton and at the
family. These names are not written anywhere: `RequestJson.lean` derives
ToJson/FromJson for `Rule`, so this list is the inductive's constructors and a
rule added there extends the protocol. `verification/tests/rule-inventory.mts`
holds the two to the same set. Expression sequents repeat their
contexts, terms and result types. The consumer checks these against the request;
this redundancy cannot substitute a different program or different claims.

Subtype arrow certificates use ordered lists of argument types. A `source`
certificate's `p` is `[domains, result]`, for example
`{"source":{"p":[[[0],[1]],[1]]}}` for a two-argument signature. A `union`
certificate contains `pre`, `a`, `b`, `suffix`, `left`, and `right`: `pre` and
`suffix` are lists of unchanged argument types, and the selected argument splits
from `a ++ b` into the two branches. `combine` retains its result types `b` and
`b'` and two branches; `empty` requires an empty type at some argument position,
not merely a zero-length argument list. Every label in these fields is bounds
checked. Graph subtype search supports native argument lists and splits any
position. Source function types, closures and calls preserve required parameter
lists, including empty lists for zero-argument thunks. There is one accepted certificate shape.

All node objects explicitly contain `expression`, `edges`, `knowledge`, `effect`
and `output`. `knowledge` and `output` each contain `cells`, `values`, and `links`. The first two are lists of
`{slot, contents, field}` facts. `contents` is a disjunction of primitive
predicates: `nul`, `undef`, `tru`, `fls`, `num`, or
`{"numLit":{"bits":"…"}}`, with the same unsigned 64-bit decimal encoding as
numeric graph clauses. The empty list is impossible. A singleton numeric fact
can weaken to `num`, never the reverse. `links` is a list of
`{cell, value, alias, field}` objects: `alias: true` means equal slot values;
`alias: false` means the named field currently contains the other slot's value. These are finite state assertions, not extra type labels.
`effect: null` selects ordinary expression evidence; a non-null effect selects
one of the checked `StepEvidence` constructors (`ordinary`, `pure`,
`typedRead`, `observedRead`, `knownValue`, `created`, `allocated`, `written`). Constructor payloads use
Lean's derived JSON encoding, with strict decode/re-encode checking; the
[graph regression](lean/Verification/ExperimentState/HeapGraphTests.lean) tests a
round trip with nonempty facts and effect evidence.

The effect checker binds to the root expression sequent and must establish exactly
`output`. Each actual outgoing edge checks fact entailment against the destination's
`knowledge`, in addition to ordinary type coverage. Effect-only continuations drop
the result slot before transferring facts. External entry requires empty knowledge.
All type labels in nested effect proofs are bounds checked. `allocated` retains its existing payload
(`slot`, `contents`, and ordinary `proof`) for either descriptor: it requires
`make code (var slot)` and checks the entire term's scope and creation proof.
The code descriptor is part of the requested term, so changing it invalidates
the evidence. `typedRead` accepts a first invariant operand shared by every
clause in a nonempty expansion of plain or callable bags. Empty expansions,
non-bag alternatives, and differing operands are rejected; its stored read
links retain the receiver descriptor. Within a source
statement, the producer derives checked facts along administrative paths. The
source consumer additionally enforces the exact entry interfaces described below.
See the [assertion rules](PROGRAM-TYPING.md#checked-expression-postconditions).

The callable expression rules use the existing term syntax. `makeCallable`
checks one initializer premise followed by one body premise per advertised
overload, each body under its argument binder. Its result has a single initial
bag contract; subtyping can add equivalent invariant requirements. `callCallable`
selects an advertised signature, while `readCallable` and `writeCallable` use
the first invariant bag operand. Every nested operand label is bounds checked.
These rules are available to calculus requests; combined callable/property
source types are not yet emitted by the source exporter.

The `ifBool` expression rule checks an ordinary `ite` with three premises:
the Boolean condition, the true arm, and the false arm. Each arm has the root's
context and requested result type. Boolean singleton unions are allowed, while
null or mixed Boolean/non-Boolean conditions are rejected. The existing
`ifTrue`/`ifFalse` rules remain the statically decided shape-test rules.
The `ifBoolVar` rule carries `trueType` and `falseType` label lists and two
arm premises. It requires an `ite` whose condition is a variable at an existing
Boolean slot. The lists must expand to the corresponding singleton clauses;
the arms use precisely the root context with that slot replaced. All payload
labels are bounds checked. The rule cannot narrow any other binding.

Requests require explicit `inputs`. Responses carry undefined literal evidence
and undefined/nullish tests in checked heap postconditions, including
ordinary-read links and writes without an old-content premise. Source bundles
carry supplemental expression proofs alongside the graph certificates.
Decode/re-encode validation requires every field and rejects any unknown
field, recursively, so a document either has the current shape or is refused.
When a shape changes, regenerate what carries it. The JSON parser and codecs still form part of the input-meaning
boundary; round-trip tests are not a proof of fidelity to external source text.

## Proved boundary and validation

`verifyJson_checked` proves that JSON acceptance yields the two decoded objects
and a successful `verify` check. `verify_claims` proves equality of the requested
point annotations and the certificate's annotations. `verify_safe` establishes
global modeled safety at every observation budget, for **any** argument
environment satisfying `inputs`, admissible world and satisfying heap. The input
contract is a premise, not inferred from SKJS's point claims. `verify_closed_safe`
specializes this to `inputs: []` and the empty heap. The theorem reuses graph
safety, including cycles, heap changes and explicit slot maps.

`produceJson` serializes generated evidence and submits it through the same JSON
consumer before returning it. The safety theorem does not require using this
producer. Search is incomplete; failure is not a proof of untypability.

`RequestJsonTests.lean` exercises serialize/parse/produce/serialize/parse/check
on a loop, a mapped diamond, a closure over a mutated cell, and a program forcing
structural overload-subtyping evidence. Negative cases alter code, claims,
requirements, maps and type labels, or add unknown fields and omit
required data. They also check that object field order does not matter.

## Source mode

The adapter accepts primitive or bounded callable parameters, initialized
`const` and `let` declarations, assignment to a `let` as an expression, nested boolean branches and returns, using variable
expressions and null/undefined/boolean literals. Every path must return. Types
may be null, undefined, boolean, true, false, unions of these, or bottom. Source
parameters may also contain the bounded function contracts below, including unions with
primitives. External cell parameters remain rejected. Local annotations and
function results can additionally contain cell contracts. Every union arm is
decoded strictly. A redundant record arm may be absorbed into an existing invariant
alternative by the checked read/write rule below; unsupported encodings are
never omitted. Other constructs
are covered by the cell and closure extensions below or rejected by the fragment
gate, including active-name shadowing and statements after an explicit return. This restriction is not a final dead-code policy.

An initialized mutable declaration has `k: "let"`, `pos`, `name`, `namePos`,
`annot` and `init`; assignment has `k: "assign"`, `pos`, `name`, `namePos` and
`rhs`. The annotation defines a private cell's invariant. An internal scope
binding records whether its slot holds a value or this cell's identity;
diagnostic descriptors carry no storage flag. Source references read the cell,
and assignment saves its RHS, writes once, then returns that saved value.
Ordinary environment claims for mutable names assert contents, not identities:
the extractor requires an invariant-based read proof or a supported primitive heap observation
checked on every incoming edge. Captured entry claims require the stable
invariant. Immutable-slot guard refinements cannot substitute cell identities.
For an unannotated initialized `let`, the first following statement's claim
supplies a candidate storage contract; the initializer and every write must
establish it. Uninitialized `let` and function-scoped `var` remain unsupported.

Assigned parameters of a stateful source function use the same private-cell
representation. Lean scans assignments, including inside nested closures, and
allocates one cell per assigned parameter on entry. Its source annotation is
the storage contract; public input types still describe the argument values.
Unassigned parameters keep their value slots. A nested closure may write a
captured outer parameter; assignment to the closure's own parameters remains
outside this lowering.

The identity scheme `id<T>(x: T): T { return x }` is also accepted, with
each distinct type parameter exported as a `param` atom. Function AST objects always
include `typeParams` (empty when the function is not generic). Each type
parameter is `{ "name": "T", "bound": null }` or `{ "name": "T", "bound": boolean }`
for `T extends boolean`; a bound may also be a `param` atom naming an earlier
parameter. Duplicate names, forward bounds and cycles are rejected. The file AST always includes `aliases` (empty when the
file declares none). `type Id<T> = T` and `type Box<T> = { value: T }` are the
admitted alias schemes; a one-argument named instantiation is an `alias` atom
`{ "a": "alias", "name": "Id", "args": [A] }`.
The adapter substitutes using the identity and cell theorems before identity
checking or ground extraction. `asBoolean<T extends boolean>(x: T): boolean { return x }`
is accepted; returning `true` as `T` is not. A generic body may copy `T`
through annotated consts and return a variable. Parameters and annotations may
name distinct declared parameters or boolean. A conversion requires identity
or a forward path through the declared bounds, so `U extends T` permits `U`
to `T` but never the reverse. A const retains its annotation after conversion.
Generic callbacks and source call-site instantiation remain outside the fragment. A file of
only these schemes still produces an empty graph evidence bundle. Both production
and consumption nevertheless check the source body, signature, and every source
entry/expression claim. Sites must match exactly, without duplicates or missing
claims. Entry inclusions, expression inclusions and binding/return contracts
are checked under rigid parameters and the declared bounds; failure reports the
source span and named inclusion. The scheme is then omitted from the ground
graph request. No per-site generic evidence is serialized yet. The neutral
source sidecar also accepts function-scoped `{ "param": "T" }` claims from
TypeScript, checked by the same generic checker against source binders and bounds.

Generate an AST with `tools/fragment-parse.mts`, and claims with SKJS's
`--emit-skjs-type-claims`. Then run:

```sh
verifier --produce-stateful-source ast.json claims.json path/to/input.ts evidence.json 8
verifier --check-stateful-source ast.json claims.json path/to/input.ts evidence.json
```

The file key must match both inputs. Evidence is a strict object
`{"functions":[...],"obligations":[...]}`, containing responses in source
function order. `obligations` has one list per function,
including empty lists, with one evidence tree per reconstructed closure-expression
or annotation judgment. Counts and root judgments must match exactly. Exported
function order does not matter. The checking command reconstructs both the
requests and required judgments itself and does not run the producer.

Native SKJS source commands first import through `SourceClaimExport` into the
same `SourceClaimJson` document and consumer used by TS. Unavailable claims stay
explicit and do not denote types. There is no separate native whole-file checker.
Ground functions lower to `SourceClaims.Function`; used candidates are resolved
with source-graph label bounds checks. Generic functions use the shared rigid
checker. See [the source-claim interface](SOURCE-CLAIMS.md).

The adapter represents boolean as the union of exact true and false labels.
[SourceTypes.lean](lean/Verification/ExperimentState/SourceTypes.lean) proves
this primitive translation exact. Unsupported types are rejected. Each source
expression's exported type remains its result claim; source annotations and
return requirements are separate synthetic-node obligations. Statement claims
supply entry contexts, and every initialized local slot requires a claimed type.
Unused extra exported bindings, such as the implicit `this`, do not create local
slots. Duplicate claim keys are rejected.

Parameter slots follow source declaration order; local declarations push ahead
of them. The exporter’s duplicate parameter signature must match source names,
order and exact translated types. The request's `inputs` come from source
annotations. A synthetic entry node carries those types and its outgoing edge
must justify the first supplied statement environment. Narrowing a parameter in
that first claim therefore cannot turn into an unproved input assumption.

The guarantee covers function bodies for all arguments satisfying their
annotations. Local expression closures and calls are supported below; graph-backed
closure bodies and verification of external callers remain outside this slice.

An `if` evaluates its condition once, keeps the exact exported expression claim,
and checks that it contains only Boolean clauses. Both arms share the compiled
continuation. Slot maps remove saved conditions and arm-local bindings on exit.
Nested branches, missing/empty arms and early-return arms are supported.

Direct and repeatedly negated Boolean variable tests refine the tested binding on their outgoing edges.
As a value, negation lowers to `ite e false true`. As a graph condition, its own
claim is checked by a supplemental proof while execution evaluates the operand
once and swaps destinations. This preserves justified current-read links as well
as immutable variable identity, and also applies to loop conditions. Non-Boolean truthiness remains unsupported. Singleton negation uses `ifKnown`
evidence with a condition proof and the selected-arm proof.
The compiler uses `branchBind`: dispatch pushes the actual tested Boolean, then
applies the target map. For `if (x)`, `x` selects this pushed slot; other variables
select their old slots. The consumer checks the Boolean singleton against the
supplied arm-entry type and ordinary subtype proofs for all other slots.

The raw encoding is `{"branchBind":{"yes":TARGET,"no":TARGET}}`, with targets
in the usual explicit format. Unlike ordinary `branch`, its maps index the
environment after pushing the result. For a destination slot selecting that
result, edge evidence must use the canonical `"subset"` marker: the consumer
then checks branch-specific singleton membership. This marker cannot refine an
untested slot. Both arm claims and later merge claims remain supplied and checked.

This rule does not derive refinements for aliases, heap contents or general
predicates. Active-name shadowing remains gated until binding identities can
distinguish hidden locals in the claim export.

Source extraction remains trusted for evaluation order, lexical binding and
claim association. The all-budget safety theorem applies to the extracted
graph, not directly to TypeScript execution. The parser is still the existing
independent parser; its format and the claim export can change as the broader
stateful fragment requires. There is no compatibility obligation to a retired fragment.

`make verify` runs the real-export integration suite. To run only that suite:

```sh
verification/run.sh --build --suite stateful-source
```

The suite checks production and independent consumption, then corrupts expression
claims, incoming environments, source annotations and input identities. Source
`while` loops now use supplied head environments with independently checked
initial and back edges. Unlabeled break/continue compile to checked mapped
transfers to the nearest loop exit/head. Tests also cover repeated condition
calls, dropping body locals and rejected transfer evidence. Mutable declarations, loops inside
closures and general partially returning nested closure arms remain gated.

## Record-contract export boundary

The SKJS claim exporter additionally supports this bounded record atom:

```json
{
  "a": "record",
  "fields": [{
    "name": "value",
    "optional": false,
    "read": {"top": false, "atoms": [{"a": "boolean"}]},
    "write": {"top": false, "atoms": [{"a": "boolean"}]}
  }],
  "indexes": {"string": "absent", "number": "absent", "symbol": "absent"},
  "call": "unknown",
  "construct": "unknown",
  "array": "unknown"
}
```

This is an SKJS export atom, **not** a new calculus type-graph clause. It records
permissions rather than choosing a heap invariant. The bounded exporter rejects
extra fields, symbols, real index signatures, positive callable/array requirements
and nested record or unresolved field types. Field read/write operands may
contain bounded callable contracts. The `indexes` object distinguishes `absent`
from `synthetic` for each key kind. Synthetic indexes are SKJS inference artifacts
excluded from runtime field lookup, not index permissions; their internal type
variables are not exported. It preserves readonly setters as `never` and marks
optional fields explicitly. `unknown` and `absent` object modes are distinct
exports, though both are compatible with the future plain-cell interpretation.

Function claims retain the substitution snapshot taken after checking the body.
Serialization follows only isolated, bound inference variables without
constraints, up to a fixed recursion limit. It reads both open and closed
existing bounds without solving, sealing or growing them. Unbound variables,
constraints, named instances and cycles remain unsupported. This exposes the
field bounds of fresh object literals without replacing their expression claims
with declaration annotations. Faithfulness of this bounded export to SKJS's
internal types is not a Lean theorem.

### Closed operation export

Each function also exports `operations`: the closed subtype and expansion
judgments SKJS accepted while checking that body. Types are serialized under
the substitution in force at the judgment, not the function's final snapshot.
Live inference variables, named instances, `unknown`, and anything outside the
fragment are omitted rather than approximated. Speculative checks on a cloned
substitution are not recorded. The independent consumer
(`--check-skjs-operations`) translates those that lower into the source
fragment and asks the existing subtype checker for a derivation. A skipped
operation is outside the fragment; an unproved one is a failed search, not a
semantic disproof. This export does not change SKJS acceptance.

```json
{
  "kind": "subtype",
  "source": {"top": false, "atoms": [{"a": "booleanlit", "v": "true"}]},
  "target": {"top": false, "atoms": [{"a": "boolean"}]}
}
```

`expand` uses the same two fields: `source` is the type before expansion,
`target` the clause view. Exact expansion is checked in both directions.

A supported multi-branch object is serialized as multiple `record` or `function`
atoms in the same `atoms` list. Every branch must export successfully; one
unsupported branch makes the whole type unavailable. No new JSON constructor is
needed, and the report retains the alternatives exactly.

`Fragment` validates and lowers all record atoms. `CellUnion.lower` absorbs a non-invariant
contract only into an existing invariant arm with weaker read requirements and
the same write invariant. Remaining arms must satisfy the invariant-cell check;
[Source claims](SOURCE-CLAIMS.md#record-alternative-absorption) specifies the
exact normalization law and its proof scope. This is not a widening
of a standalone refined cell claim.

`CellClaims.decodeShape` validates each single-record shape. `Fragment`
lowers read and write operands, including callables, to the same graph table and
requires equal invariant label lists after union absorption. Unknown fields and
unsupported operands reject the whole contract. `CellClaims.translate` retains
the primitive specialization and its exact claim-membership theorem, also used
for primitive current-content observations. The reference-label theorem applies
to arbitrary graph operands; neither theorem establishes TypeScript
record-to-reference correspondence or excludes accessor-backed runtime objects.

`cell_claim_tests` exercises real SKJS exports and corrupted contracts as part
of `make verify`. Allocation probes check Boolean, singleton and contextually
widened field bounds; the alias-write probe retains both named cell contracts.
Source cells now reach certificate production and independent consumption.
Their source correspondence remains a reviewed compilation obligation.

## Cell source lowering

Use `fragment-parse.mts <file.ts>` for the extended source gate. It accepts
only plain `{ value: e }` allocations, `.value` reads and assignments, with the
required invariant-cell contracts above. Methods, accessors, computed keys,
spreads, extra fields and optional access are rejected. Cell parameters are
also rejected until a plain-data boundary for external objects is supplied.

The stateful input decoder keeps types separate from the earlier primitive AST.
Every initializer, receiver, RHS, read and assignment expression consumes its
own claimed type. The request graph uses the four primitive labels and sixteen
reference labels, one for each primitive invariant. `CellClaims.reference_exact`
proves that the selected label has exactly the accepted invariant's meaning.

Expression nodes bind evaluated values into temporary slots. The compiler
executes the receiver before the RHS and executes each once. A calculus write
returns null; the subsequent node returns the saved RHS, preserving JavaScript's
assignment-expression result. Destination maps remove temporary slots while
preserving live source bindings. Cell effects can occur in branches and nested
expressions; the existing node and incoming-edge checks justify their claims.
The reference invariant is stable across writes; no heap-content refinement or
analysis is added.

## Expression closures and calls

The bounded function atom is:

```json
{
  "a": "function",
  "params": [{"top": false, "atoms": [{"a": "null"}]}],
  "result": {"top": false, "atoms": [{"a": "boolean"}]},
  "construct": "unknown",
  "array": "unknown"
}
```

The exporter preserves the ordered list of free required parameters and the result. It rejects
`this` requirements, generics, optional/rest parameters, unsupported fields, indexes, positive
construct requirements and record-valued operands. Arrow arguments and results
may recursively union bounded function contracts with the
supported primitives null, undefined, true and false. The SKJS exporter uses
bounded recursion, and the tsc producer applies a depth limit when translating
nested operands. No unsupported union alternative is discarded.

`Fragment.callableType` lowers every supported operand to graph labels.
See [callable integration](DESIGN.md#callable-integration) for the proof boundary.

Source lambda ASTs carry `"params": [{"name": "x", "type": T}, ...]`;
applications carry `"args": [expression, ...]` alongside `"callee"`.
Both use empty lists for zero-argument forms. A lambda's descriptor records its
parameter count, with those bindings before captured variables. Calls evaluate
the callee first and actuals left to right; checked signatures require the exact
actual count. No synthetic undefined actual, anonymous parameter, or source
claim is introduced for an empty list. Optional/rest parameters, spread actuals,
`arguments`, receiver-dependent bodies and argument-count introspection remain excluded.

A strict `typeof e === "function"` or `!==` comparison has source AST shape
`{"k":"functionTest","pos":[start,end],"equal":true,"e":operand}`.
Reversed operands use the same shape. The trusted parser checks the `typeof`
operator and literal; the adapter checks the operand and Boolean predicate
claims and lowers through `isFun`. Only an immutable identifier operand can
refine a binding. Other `typeof` comparisons and general string expressions
remain outside the source fragment.

Source arrows require explicit parameter and result annotations. Bodies compose
literals, variables, cell allocation, reads, assignments and calls, including
nested expression arrows with required parameter lists. Each expression's
claim is checked as a separate exact sequent in its lexical context. The body
also has to satisfy the declared result. A narrower body claim with a wider
result annotation is supported when both judgments are derivable. A block with
exactly one `return e;` is supported too. The AST represents its body as
`{"k":"returnBody","pos":[start,end],"e":...}`. The statement span selects its
exported environment, whose bindings must each be justified by a variable typing
proof under the captured context and parameter. The expression is checked using
that supplied environment, including when it forgets precision. Missing entry
claims and unjustified types on unused bindings are rejected. Straight-line
blocks may precede that return with initialized consts or expression statements. These use `letBody` nodes with `pos`, `name`, `annot`, `init` and `body`;
an empty name denotes a discarded effect result. The consumer reconstructs
statement-entry and annotation obligations, retaining initializer precision in
the bound slot. Anonymous effect slots retain their types independently of the
export's named environment. A terminal `if/else` is represented by `ifBody`,
with `pos`, `result` (the enclosing result annotation), `cond`, `then` and `else_`.
Terminal arms recursively end in returns; prefixes may contain consts, effects
and branches whose arms both fall through.
Its position selects the checked entry environment, not an expression claim.
Variable conditions (including negations, with swapped arms for odd parity) use
`ifBoolVar`; other Boolean conditions use `ifBool`.
Arm statement claims are checked against those justified contexts.

Source ternaries use `{"k":"conditional","pos":[start,end],"cond":...,"then":...,"else_":...}`.
Unlike the statement wrapper, this node selects its own expression claim, not a
statement-entry environment. Its condition and both arms retain their exact
expression claims. Internally both forms share conditional proof construction:
Boolean-variable and primitive-tag refinements use the existing rules, while general
conditions use ordinary Boolean elimination. Effects execute in the condition
and selected arm only. No new calculus rule or source type label is introduced.

Short-circuit operators retain the binary AST shape
`{"k":"bin","pos":[start,end],"op":"&&"|"||","l":...,"r":...}`.
The expression and both operands require claims; the left operand must be Boolean.
Statement guards use graph paths while retaining the complete condition claim.
The [derived typing forms](PROGRAM-TYPING.md#derived-source-forms) specify their
proof construction and evaluation order.

Null coalescing uses `{"k":"coalesce","pos":[start,end],"left":...,"right":...}`.
The overall expression and both operands select exact expression claims. Lowering
saves the left result in a let slot, then uses nullish testing and `unionVar`
to check the fallback or return the saved value. False takes the latter path.
For a syntactic immutable variable on the left, its name refers to the saved slot
inside the fallback; its original slot becomes anonymous. This exposes the proved
nullish refinement without claiming an alias for reads or calls. Both null and
undefined select the fallback; false is preserved.

For fall-through branches, `ifBody` has the administrative null result type and
each arm ends in `{"k":"doneBody","pos":[start,end]}`. The sentinel is not a
source expression or a claimed JavaScript result. A `seqBody` with `pos`, `init`
and `body` evaluates this conditional, discards its result and runs one shared
continuation. The continuation uses an anonymous result slot plus the outer
context; arm-local slots cannot escape. No synthetic source expression claim
is requested for either administrative node. Their generated typing obligations
are nevertheless independently checked, as are every source expression and
statement-entry environment.

When one arm returns on every path and the other is return-free, the parser
places the continuation only inside the surviving `ifBody` arm. A nonempty
falling arm is first compiled to a `seqBody` initializer, keeping its local
bindings out of the continuation. Empty falling arms resume directly. The
existing branch rule justifies the surviving path's immutable Boolean
refinement, including at the continuation's supplied entry environment. No new
AST tag, type claim or calculus rule is needed. General partially returning
nested arms, unreachable continuations and active-name shadowing remain gated. Standalone field-test claims with unequal read/write meanings remain outside
the invariant-cell slice; exact union absorption does not admit them on their own.

Proof recipes are internal producer data, not wire fields. Their construction
and reuse are described in [source integration](DESIGN.md#source-integration-current-slice-and-next-milestone).

Source assertion requirements are reconstructed from the source/claim inputs,
not read from the certificate. Every statement entry requires certificate input
knowledge to equal exactly its supplied current predicates, with empty value facts
and links. An entry without observations requires empty knowledge. Expression
result checkpoints inside the statement require entailment instead. The source
consumer checks both policies alongside ordinary graph and supplemental proofs;
every incoming edge is checked. Neither the cut labels nor their interfaces are
chosen by the certificate. See
[the source checkpoint rules](PROGRAM-TYPING.md#source-observation-checkpoints).

The source bundle carries these supplemental proofs alongside the graph
certificates. The consumer checks their syntax, scope, exact root judgment and
rule derivation using `ExpressionClaims.checkAll`. Dropping a proof, adding a
proof or substituting a valid proof of a different judgment is rejected.
The whole lambda is also checked by the ordinary program certificate.
Callable parameters are admitted at their source annotations; named top-level
calls and external cell parameters remain outside the fragment. Evaluation order,
capture lowering and assignment temporaries are described in
[source integration](DESIGN.md#source-integration-current-slice-and-next-milestone).

### Singleton comparisons

Source binary forms with `op` equal to `===` or `!==` are accepted when either
operand has a checked singleton null, undefined or numeric type. Lean resolves the latter case using the common source claims;
the operand obligation must prove that singleton, so a forged claim cannot
justify replacing equality by a tag test. Both operands are evaluated in source order and both
retain their expression obligations. The comparison lowers to the corresponding primitive
test and Boolean conditional over the saved operand. Numeric tests use
`{"numEq":{"bits":"…"}}` as the shared `Tag` representation. They implement
[Number::equal](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-equal):
the two signs of zero compare equal, and NaN never compares equal. `unionVar`
evidence handles finite unions with known outcomes; a broad `number` operand
remains unsupported by this source proof construction. Unknown outcomes retain
the whole type on both branches, never establish the false branch. The same lowering is available inside a supported closure.

Top-level branches and loop heads also refine a syntactically identified immutable
variable. Negations and either operand order are supported. The original
condition and its claims are checked before tag dispatch on the same immutable
value; reads and calls cannot supply an alias refinement.

The graph encoding is `{"tagBind":{"test":"isNul","yes":TARGET,"no":TARGET}}`.
Tags use the existing term-tag encoding. Dispatch pushes the observed value;
maps select from that extended environment. Each edge carries ordinary subtype
evidence from the conservatively tag-filtered type for slot zero, and ordinary
subtype evidence from the unchanged type for every other slot. Both destinations
are checked. The observation comes from execution, never from evidence.

`tests/stateful-source/null-guards.ts` exercises this integration. Closure null
guards use existing expression certificate forms (`letE`, `unionVar`, `ifTrue` /
`ifFalse`), preserving condition evaluation and all source claims. No new closure
wire form is needed. A plain cell read tested against null/undefined can also
be saved and reused within branches with no calls, writes, allocations or nested
closures. Current-content assertions must follow from that saved value, and
source claims are checked separately from any stronger return evidence.
Other strict comparisons, loose equality, property refinement across effects
and loops inside closures remain source boundaries.

A function with one required invariant `value` field is exported as
`{"a":"callable","function":F,"bag":B}`, where `F` is the bounded function
atom above and `B` is a bounded record atom with `call: "unknown"`. Both describe
the same object. The source decoder requires equal read/write field contracts
and lowers to the native graph callable clause; current-content field assertions
and nested callable objects are outside the fragment.

The initialization AST is
`{"k":"withValue","pos":[start,end],"fn":arrow,"initial":objectLiteral,"functionType":F,"bagType":B}`.
Here the annotation fields are claim types, not atoms. The parser emits this only
for standard `Object.assign<F, B>(freshArrow, {value: initializer})`, with no
shadowed `Object`, extra arguments, spread or accessors. Both explicit type
arguments and both source expression claims are independently checked before
constructing the initialized callable.

Local-arrow `.call` expressions use
`{"k":"callWithReceiver","pos":[start,end],"callee":expression,"receiver":expression,"args":[expression,...]}`.
The trusted parser requires a source-created arrow (possibly initialized with a
field) or an immutable lexical alias of one. Parameters, arbitrary call results,
optional access/calls, spreads and omitted receivers are refused. The standard
intrinsic is a source-boundary assumption, not inferred from a call signature.
The adapter evaluates the callee, receiver and actuals in that order, checking
every operand claim. It discards only the receiver value and invokes the existing
native call rule with exactly the listed actuals. No receiver binding is added
to the arrow body; this slice does not implement ordinary function `this`.

A bound local arrow uses the same operand fields as `callWithReceiver`, with
`"k":"bindWithReceiver"`: `callee`, `receiver`, and `args` (the saved prefix).
The decoder requires that exact shape. The source gate establishes a local arrow
or bound-arrow target, without optional calls, spread or missing receivers.
The result claim must be a single free signature. Its parameters describe the
remaining actuals; their ordered concatenation with the bound prefix must satisfy
the target's exact signature. The adapter saves operands once and creates a
native closure. Binding every parameter yields an ordinary zero-argument closure.
