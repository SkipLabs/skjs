# Stateful calculus request protocol

The existing verifier binary now accepts a versioned JSON request for the
stateful calculus, separately from its derivation certificate. This is a
consumer boundary for extracted programs. It is **not** a decoder for SKJS's
source-associated claims, and it does not certify TypeScript text by itself.

The source-facing F0 invocation is unchanged. Both modes use the same executable;
stateful request mode is an explicit integration entry point.

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
| Invariant reference with optional additional contract requirements | `{"refs":{"first":[1],"rest":[]}}` |
| Intersection of arrows | `{"arrs":{"arrows":[[[0],[1]],[[1],[0]]]}}` |

The arrow example contains two domain/result pairs. References and arrow
operands may point back to the same finite graph, representing guarded regular
recursion. The request already contains normalized clauses; a source type
extractor must use the proved normalization interface when translating positive
formulas. No string, number, boolean singleton, generic or unsupported-type
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

The codec names and fields are part of protocol version 1. A change to their
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

## What extraction still needs to establish

A TypeScript extractor must construct the actual graph, preserve evaluation
order and lexical binding, and associate SKJS claims with the correct nodes.
It must distinguish source requirements, exported claims and intermediate types
chosen by the producer. This protocol does not perform those tasks.

In particular, SKJS's primitive claim encoding can distinguish `true` and
`false`, while the current positive graph has only `boolean`. Mapping either
singleton to `boolean` would weaken the claim. A source adapter must reject
unsupported claims, establish their full meaning through an explicit additional
check, or extend the calculus with sound rules for those types. It must not
silently widen them and report that the original claims were verified.

The first source integration should therefore specify exact supported type
translation before broadening syntax. The current source parser also rejects
mutable declarations, loops and closures, so the JSON round trips above are
calculus integration tests, not a claim that those TypeScript features now pass
through the source pipeline.
