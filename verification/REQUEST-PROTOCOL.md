# Stateful calculus request protocol

The existing verifier binary now accepts a versioned JSON request for the
stateful calculus, separately from its derivation certificate. This is a
consumer boundary for extracted programs. It is **not** a decoder for SKJS's
source-associated claims, and it does not certify TypeScript text by itself.

Raw request mode and the source adapter below use the same executable. The
existing F0 invocation is also available during integration.

## Run a request

Build from `verification/lean`:

```sh
lake build
```

Save this minimal request as `request.json`:

```json
{
  "version": 2,
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
| `version` | Exactly `2`. |
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
| Invariant reference with optional additional contract requirements | `{"refs":{"first":[1],"rest":[]}}` |
| Intersection of arrows | `{"arrs":{"arrows":[[[0],[1]],[[1],[0]]]}}` |

The arrow example contains two domain/result pairs. References and arrow
operands may point back to the same finite graph, representing guarded regular
recursion. The request already contains normalized clauses; a source type
extractor must use the proved normalization interface when translating positive
formulas. No string, number, generic or unsupported-type
fallback is supplied by this protocol.

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
supply a default. The expression and continuation constructors are defined in
`Language.lean` and `ControlFlow.lean`; their codecs live in
[RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean).

The evidence file is an object with `version: 2` and `certificate`, a list of
`NodeEvidence` objects. Each node supplies its expression derivation tree and
one subtype-evidence list per outgoing edge. Expression sequents repeat their
contexts, terms and result types. The consumer checks these against the request;
this redundancy cannot substitute a different program or different claims.

Protocol version 2 requires explicit `inputs`. Requests, responses and source
bundles use version 2; version 1 is rejected. There is one maintained protocol.
Decode/re-encode validation rejects unknown fields and missing fields,
recursively. The JSON parser and codecs still form part of the input-meaning
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
requirements, maps, versions and type labels, or add unknown fields and omit
required data. They also check that object field order does not matter.

## Source mode

The adapter accepts primitive parameters, initialized `const` declarations,
nested boolean branches and returns, using variable expressions and null/boolean
literals. Every path must return. Types
may be null, boolean, true, false, unions of these, or bottom. Other constructs
are rejected by the current slice gate, including source calls, closures, active-name
shadowing and statements after an explicit return. This restriction is not a final dead-code policy.

Generate an AST with `tools/parse-source.js`, and claims with SKJS's
`--emit-skjs-type-claims`. Then run:

```sh
verifier --produce-stateful-source ast.json claims.json path/to/input.ts evidence.json 8
verifier --check-stateful-source ast.json claims.json path/to/input.ts evidence.json
```

The file key must match both inputs. Evidence is a strict object
`{"version":2,"functions":[...]}`, containing ordinary responses in source
function order. Exported function order does not matter. The checking command
reconstructs the requests itself and does not run the producer.

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
annotations. It does not yet provide source-level calls, graph-backed callable
closures, or verification of external callers.

An `if` evaluates its condition once, keeps the exact exported expression claim,
and checks that it contains only Boolean clauses. Both arms share the compiled
continuation. Slot maps remove saved conditions and arm-local bindings on exit.
Nested branches, missing/empty arms and early-return arms are supported.

Direct Boolean variable tests refine the tested binding on their outgoing edges.
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
stateful slice requires. There is no F0 compatibility obligation.

`make verify` runs the real-export integration suite. To run only that suite:

```sh
verification/run.sh --build --suite stateful-source
```

The suite checks production and independent consumption, then corrupts expression
claims, incoming environments, source annotations and input identities. Source
loops, mutable declarations and closures are not connected yet; their raw request
tests remain calculus tests.

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
  "call": "unknown",
  "construct": "unknown",
  "array": "unknown"
}
```

This is an SKJS export atom, **not** a new calculus type-graph clause. It records
permissions rather than choosing a heap invariant. The bounded exporter rejects
extra fields, symbols, indexes, positive callable/array requirements and nested
or unresolved field types. It preserves readonly setters as `never` and marks
optional fields explicitly. `unknown` and `absent` object modes are distinct
exports, though both are compatible with the future plain-cell interpretation.

`CellClaims.translate` validates this shape and requires the read and write
types to normalize to the same supported primitive set. Unknown fields and
unsupported types are rejected. Its theorem connects both supplied primitive
types to that set's meaning. The candidate cell interpretation is an invariant
reference to that meaning; the theorem does not yet establish a TypeScript
record-to-reference correspondence or exclude accessor-backed runtime objects.

`cell_claim_tests` exercises real SKJS exports and corrupted contracts as part
of `make verify`. The allocation/alias-write probe retains the named cell
contracts, while the object literal's own claim remains unsupported. The source
compiler still rejects cell syntax. Plain-data allocation, property reads/writes
and their source correspondence are the next integration work.
