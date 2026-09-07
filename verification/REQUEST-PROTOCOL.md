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
  "version": 1,
  "types": [["nul"]],
  "program": [{"expression": "nul", "continuation": "ret"}],
  "claims": [{"context": [], "type": [0]}],
  "result": [0],
  "start": 0
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
| `version` | Exactly `1`. |
| `types` | A finite array of normalized type-graph nodes. Its array positions are type labels. |
| `program` | A finite array of calculus nodes. Its positions are control-flow labels. |
| `claims` | One entry context and expression-result type per program node, in the same order. |
| `result` | The required result type of the graph. |
| `start` | The designated control-flow entry label, whose claimed context must be empty. |

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

The evidence file is an object with `version: 1` and `certificate`, a list of
`NodeEvidence` objects. Each node supplies its expression derivation tree and
one subtype-evidence list per outgoing edge. Expression sequents repeat their
contexts, terms and result types. The consumer checks these against the request;
this redundancy cannot substitute a different program or different claims.

The codec names and fields are part of protocol version 1. The `boolLit` clause
and `truLit`/`flsLit` evidence rules extend this initial protocol additively:
existing tags retain their meaning, and older consumers reject the new tags. A change to their
meaning or shape requires an explicit protocol decision. Decode/re-encode
validation rejects unknown fields and missing fields, recursively, rather than
silently ignoring future flags or defaulting omitted fields. The JSON parser
and codecs still form part of the input-meaning boundary; round-trip tests are
not a proof of fidelity to external source text.

## Proved boundary and validation

`verifyJson_checked` proves that JSON acceptance yields the two decoded objects
and a successful `verify` check. `verify_claims` proves equality of the requested
point annotations and the certificate's annotations. `verify_safe` establishes
global modeled safety at every observation budget. It reuses the graph theorem,
including its treatment of cycles, heap changes and explicit slot maps.

`produceJson` serializes generated evidence and submits it through the same JSON
consumer before returning it. The safety theorem does not require using this
producer. Search is incomplete; failure is not a proof of untypability.

`RequestJsonTests.lean` exercises serialize/parse/produce/serialize/parse/check
on a loop, a mapped diamond, a closure over a mutated cell, and a program forcing
structural overload-subtyping evidence. Negative cases alter code, claims,
requirements, maps, versions and type labels, or add unknown fields and omit
required data. They also check that object field order does not matter.

## Source mode

The first adapter accepts closed functions with initialized `const` declarations
and a final return, using variable expressions and null/boolean literals. Types
may be null, boolean, true, false, unions of these, or bottom. Other constructs
are rejected by the current slice gate, including branches, parameters and
statements after return. This restriction is not a final dead-code policy.

Generate an AST with `tools/parse-source.js`, and claims with SKJS's
`--emit-skjs-type-claims`. Then run:

```sh
verifier --produce-stateful-source ast.json claims.json path/to/input.ts evidence.json 8
verifier --check-stateful-source ast.json claims.json path/to/input.ts evidence.json
```

The file key must match both inputs. Evidence is a strict object
`{"version":1,"functions":[...]}`, containing ordinary responses in source
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
