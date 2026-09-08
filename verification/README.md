# Verification experiment

This experiment checks SKJS's type assignments with a small verifier written
in Lean. SKJS exports **type claims**; the verifier reads the source
independently and checks that those claims justify the program's typing.

The implemented fragment is called **F0**: first-order functions over primitive
values, with type narrowing. A stateful calculus and certificate consumer are
also implemented, with a source adapter for parameterized null/boolean functions. Verification
runs separately from ordinary SKJS checking.

## Run

Prerequisites are Node, the Lean toolchain pinned in
[lean-toolchain](lean/lean-toolchain), and Docker (or a devcontainer).
Install the JavaScript dependency and build SKJS before the first run:

```sh
(cd verification/tools && npm install)
make build-in-docker
```

Then run:

```sh
make verify-programs
```

This builds the Lean verifier and checks the TypeScript program corpus using
the existing SKJS binary. Rebuild SKJS after changing its implementation.
Progress appears immediately, with a result for each file:

```text
Building verifier...
Checking TypeScript programs...
  programs/accept/bool_ops.ts ... verified
  ...
Programs: 15 passed, 0 failed
```

Failures include diagnostics. For additional details and build output:

```sh
make verify-programs VERBOSE=1
```

The verifier's claim validation tests run separately. They start with a valid
SKJS claim set and alter it to test individual validation requirements:

```sh
make verify-claims       # claim validation tests
make verify              # corpus, claim validation and stateful source integration
```

These are regression tests that exercise different things: the
TypeScript corpus tests the pipeline on real programs; claim validation tests
target the verifier's response to supplied claims. The stateful source suite also
checks real exports through certificate production and independent consumption.
A separate cell-contract test checks the read/write export boundary; it does
not yet certify cell source programs. Use the combined command for
the full experiment check.

To run tests without rebuilding the verifier:

```sh
verification/run.sh early_return
verification/run.sh --verbose
verification/run.sh --skjs target/host/dev/skjs.some-variant early_return
```

`make verify` is the stable command as coverage grows.
F0 is a name for language coverage, not a version of the public command.

## Stateful calculus requests

The same verifier binary can produce and independently check serialized
stateful calculus evidence. See [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md) for a
complete minimal request and commands. This interface takes an extracted graph
and point annotations. A source mode also connects the independent parser and
SKJS exports to this consumer for **functions with primitive parameters, initialized `const`
bindings, nested branches and returns**, using variables, null and boolean
literals. Both falling-through arms share one continuation.
Boolean singleton claims are translated exactly, including refinements from
direct Boolean variable tests. Active-name shadowing remains gated. See the protocol's source-mode
commands and limitations; source loops, closures and mutation are not connected yet.

## What runs

1. [parse-source.js](tools/parse-source.js) uses the TypeScript parser to produce an
   independent syntax tree. It rejects constructs outside the fragment.
2. SKJS checks the source and emits its claims with `--emit-skjs-type-claims`.
3. The [Lean verifier](lean/Verification/Verify.lean) checks those claims
   against the source and the calculus's rules.
4. [runtime-check.js](tools/runtime-check.js) runs selected calls in Node and
   checks their returned values against the source return types.

The Node step is a test, not part of the proof. It samples argument values,
with at most 24 combinations per function; it does not compare complete
execution traces with the Lean evaluator.

## What is supported

The source fragment has `string`, `number`, `boolean`, `null`, `undefined`,
literal types and unions. Functions have annotated parameters and return types
and may call other functions in the same file.

Statements are `const`, `if` and `return`. Expressions include variables,
literals, `typeof`, `===`, `!==`, `!`, `&&`, `||` and function calls.
Conditions and boolean operators require booleans; the harness passes
`--truthiness boolean` to SKJS.

There are no mutable locals, loops, objects, closures or generics. Branches
may fall through and merge; a function may not fall off the end without
returning. Statements that cannot run are not part of the verified program and
carry none of its obligations. A declaration binds throughout its block, so
reading one before its declaration is rejected, as it is in JavaScript.

## What is established

The Lean development proves that verifier acceptance implies the program
satisfies the calculus's typing rules. Calculus soundness then guarantees that,
under its execution model, a call with arguments inside the declared parameter
types cannot get stuck and any returned value is inside the declared return
type. Termination is not guaranteed.

Applying that result to JavaScript also depends on the parser, decoders,
toolchain and fidelity of the execution model. Numeric edge cases still need
attention; the current Node samples are not a complete model validation.

Acceptance does not prove that the claims faithfully describe SKJS's internal
state, or that every inconsistent claim set would be rejected. The
[design document](DESIGN.md) explains these distinctions,
the proof boundary and what extending the fragment requires.

## Tests

| Location | Expected result |
|---|---|
| [tests/programs/accept](tests/programs/accept) | SKJS and verification accept; sampled Node calls satisfy the return types. |
| [tests/programs/reject](tests/programs/reject) | SKJS rejects an ordinary type error. |
| [tests/programs/outside](tests/programs/outside) | The independent front end rejects an unsupported construct. |
| [tests/programs/known-unsound](tests/programs/known-unsound) | SKJS accepts, verification rejects for the expected reason, and Node finds a violation. |
| [type-claims.js](tests/type-claims.js) | Altered claims or source identifiers fail the intended checks. |

The last group tests the receiver of the claims, not the exporter.
It distinguishes obligations from input validation. There is no standing test
that deliberately breaks SKJS and checks whether the resulting mistake shows up
in its claims.

## Code map

To find the languages and their meaning, read `Values.lean`, `Types.lean`, and
`Programs.lean`. These define the calculus. `SourceAst.lean` defines the supported
TypeScript source representation; `Lowering.lean` compiles it into the calculus.
These files contain definitions without proof developments, and they are the
ones the soundness statement reaches. The
[design document](DESIGN.md#reviewing-the-definitions) explains this boundary.

| File | Responsibility |
|---|---|
| [Values.lean](lean/Verification/Calculus/Values.lean) | Shared runtime values. No project imports. |
| [Types.lean](lean/Verification/Calculus/Types.lean) | Type syntax and its meaning as sets of values. |
| [Programs.lean](lean/Verification/Calculus/Programs.lean) | Core calculus: expressions, control-flow graphs, and their execution semantics. |
| [SourceAst.lean](lean/Verification/SourceAst.lean) | TypeScript source AST with locations. |
| [Lowering.lean](lean/Verification/Lowering.lean) | Source AST → control-flow graph, resolving lexical binding to slots. Start at `lowerProg`. |
| [TypeOperations.lean](lean/Verification/Calculus/TypeOperations.lean) | Type constructors, comparisons, intersection and difference, with correctness proofs. |
| [Narrowing.lean](lean/Verification/Calculus/Narrowing.lean) | Type environments, branch refinement and its correctness proofs. |
| [Typing.lean](lean/Verification/Calculus/Typing.lean) | Environment implication, edge and node typing, and program soundness. |
| [Calculus.lean](lean/Verification/Calculus.lean) | Import-only entry point for the calculus modules. |
| [Obligation.lean](lean/Verification/Obligation.lean) | The relations to establish, their meaning, and a proved discharge procedure. |
| [Verify.lean](lean/Verification/Verify.lean) | Assign each node the claim at the statement it came from, discharge the node and edge obligations, and prove acceptance implies typing. |
| [SkjsTypeClaims.lean](lean/Verification/SkjsTypeClaims.lean) | The claim format, claim lookup and signature input validation. |
| [JsonDecode.lean](lean/Verification/JsonDecode.lean) | JSON decoding. |
| [Tests/](lean/Verification/Tests) | One test file per module, named after it; each header says what it pins and whether it is trusted. Built with the verifier. |
| [SkjsTypeClaims.sk](../src/SkjsTypeClaims.sk) | Emit SKJS's claims: expression types, statement environments and function signatures. |
| [run.sh](run.sh) | Build when requested, run the corpus and claim validation tests, and report results. |

One directory is a design investigation rather than part of the verifier. It
builds with everything else but is not yet used by the production verifier.

| Directory | Responsibility |
|---|---|
| [ExperimentState/](lean/Verification/ExperimentState) | The semantics the calculus is heading toward: stratified worlds, the guarded fixed point, mutable state and operational safety. Guide in [SEMANTICS.md](SEMANTICS.md); positive normalization, declarative subtype rules and checked certificates in [POSITIVE-TYPES.md](POSITIVE-TYPES.md); proved program rules in [PROGRAM-TYPING.md](PROGRAM-TYPING.md). |
