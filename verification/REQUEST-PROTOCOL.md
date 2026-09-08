# Stateful calculus request protocol

The verifier accepts a versioned JSON request for the
stateful calculus, separately from its derivation certificate. This is a
consumer boundary for extracted programs. It is **not** a decoder for SKJS's
source-associated claims, and it does not certify TypeScript text by itself.

Raw requests and the source modes below use the same executable and consumer.

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

Protocol version 2 requires explicit `inputs`. Raw requests and responses use
version 2. Source bundles use version 3 to include supplemental expression proofs;
older source bundles are rejected.
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
are covered by the cell and closure extensions below or rejected by the slice
gate, including active-name shadowing and statements after an explicit return. This restriction is not a final dead-code policy.

Generate an AST with `tools/parse-source.js`, and claims with SKJS's
`--emit-skjs-type-claims`. Then run:

```sh
verifier --produce-stateful-source ast.json claims.json path/to/input.ts evidence.json 8
verifier --check-stateful-source ast.json claims.json path/to/input.ts evidence.json
```

The file key must match both inputs. Evidence is a strict object
`{"version":3,"functions":[...],"obligations":[...]}`, containing ordinary version-2
responses in source function order. `obligations` has one list per function,
including empty lists, with one evidence tree per reconstructed closure-expression
or annotation judgment. Counts and root judgments must match exactly. Exported
function order does not matter. The checking command reconstructs both the
requests and required judgments itself and does not run the producer.

Internally, SKJS exports pass through `SkjsSourceClaims.translate` into
`SourceClaims.Function`, whose candidates are calculus type labels or explicit
decoding failures. `extractNormalizedFn` is the same extraction path for direct
in-memory producers. Used candidates are resolved with source-graph label bounds
checks. This does not introduce a serialized claim format or change the CLI;
see [the proposed source-claim interface](CLAIM-INTERFACE.md).

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
Negation lowers to `ite e false true`. For odd parity, the compiler recovers the
original variable value and swaps destinations; it never re-evaluates the source
operand. This also applies to loop conditions. Non-Boolean truthiness remains unsupported. Singleton negation uses `ifKnown`
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
stateful slice requires. There is no compatibility obligation to a retired fragment.

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
and nested or unresolved field types. The `indexes` object distinguishes `absent`
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

`CellClaims.translate` validates this shape and requires the read and write
types to normalize to the same supported primitive set. Unknown fields and
unsupported types are rejected. Its theorem connects both supplied primitive
types to that set's meaning. The cell interpretation is an invariant
reference to that meaning; the theorem does not yet establish a TypeScript
record-to-reference correspondence or exclude accessor-backed runtime objects.

`cell_claim_tests` exercises real SKJS exports and corrupted contracts as part
of `make verify`. Allocation probes check Boolean, singleton and contextually
widened field bounds; the alias-write probe retains both named cell contracts.
Source cells now reach certificate production and independent consumption.
Their source correspondence remains a reviewed compilation obligation.

## Cell source lowering

Use `parse-source.js <file.ts>` for the extended source gate. It accepts
only plain `{ value: e }` allocations, `.value` reads and assignments, with the
required invariant-cell contracts above. Methods, accessors, computed keys,
spreads, extra fields and optional access are rejected. Cell parameters are
also rejected until a plain-data boundary for external objects is supplied.

The stateful input decoder keeps types separate from the earlier primitive AST.
Every initializer, receiver, RHS, read and assignment expression consumes its
own claimed type. The request graph uses the three primitive labels and eight
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

The exporter preserves one free required parameter and the result. It rejects
`this` requirements, generics, optional/rest parameters, fields, indexes, positive
construct requirements and nested operand types. The Lean source slice further
requires both the parameter and result to be supported primitive sets over
null, true and false. `FunctionClaims.translate_exact` identifies the selected label's
meaning with the corresponding arrow in the existing world-indexed semantics.
This does not assert equivalence with SKJS's full structural function types.

Source arrows require explicit parameter and result annotations. Bodies compose
literals, variables, cell allocation, reads, assignments and calls, including
nested expression arrows under the same signature limits. Each expression's
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
nested arms, unreachable continuations and active-name shadowing remain gated. Field tests that produce unequal
read/write claims remain outside the invariant-cell slice.

For closure expressions the producer follows explicit proof recipes, retaining
the initializer's claimed type at each source let and choosing known types for
administrative temporaries. Context changes become explicit variable coercions.
Only subtype obligations still require search. It can reuse an already produced
supplemental proof with an exact matching root judgment in the graph certificate.
The independent consumer and source bundle format are unchanged.

Source bundle version 3 carries these supplemental proofs alongside the graph
certificates. The consumer checks their syntax, scope, exact root judgment and
rule derivation using `ExpressionClaims.checkAll`. Dropping a proof, adding a
proof or substituting a valid proof of a different judgment is rejected.
Assignments save the receiver and RHS once, perform the calculus write, and
return the saved RHS; anonymous slots preserve lexical binding and evaluation
order. The whole lambda is also checked by the ordinary program certificate.

A closure is lowered to a lambda with its parameter in slot zero and captures
shifted by one. Calls accept one ordinary argument and evaluate callee then
argument, preserving both claims. Closures may be stored in local constants,
called after alias writes, or returned. External function parameters and named
top-level calls remain outside this source slice. Capture and source evaluation
order remain part of the reviewed compiler boundary; calculus lambda/application
soundness is proved.

### Null predicates

Source binary forms with `op` equal to `===` or `!==` are accepted when either
operand is a null literal. Both operands are evaluated in source order and both
retain their expression obligations. The comparison lowers to an existing null
shape test and Boolean conditional over the saved operand. `unionVar` evidence
allows tag dispatch over a primitive union; no new term or reference semantics
is introduced. The same lowering is available inside a unary closure.

This currently establishes predicate results, not the tested variable's narrowed
type at graph successors. `tests/unsupported/null-guard.ts` is accepted by SKJS
but rejected at an incoming-edge obligation by the current verifier. Other strict
comparisons and loose equality remain explicit source boundaries.
