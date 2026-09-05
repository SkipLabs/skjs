# Verification experiment

This experiment checks SKJS's type assignments with a small verifier written
in Lean. SKJS exports **type claims**; the verifier reads the source
independently and checks that those claims justify the program's typing.

The implemented fragment is called **F0**: first-order functions over primitive
values, with type narrowing. Later fragments are planned, not implemented.
Verification runs separately from ordinary SKJS checking.

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
make verify              # program corpus and claim validation tests
```

Both groups are regression tests, but they exercise different things: the
TypeScript corpus tests the pipeline on real programs; claim validation tests
target the verifier's response to supplied claims. Use the combined command for
the full experiment check.

To run tests without rebuilding the verifier:

```sh
verification/run.sh early_return
verification/run.sh --verbose
verification/run.sh --skjs target/host/dev/skjs.some-variant early_return
```

`make verify` is the stable command as coverage grows.
F0 is a name for language coverage, not a version of the public command.

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
must return rather than merge: an `if` without an `else` may continue on
its false path, but its true branch must return.

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
the proof boundary and the next experiment.

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
TypeScript source representation; `Lowering.lean` maps it into the calculus.
These files contain definitions without proof developments. The
[design document](DESIGN.md#reviewing-the-definitions) explains this boundary.

| File | Responsibility |
|---|---|
| [Values.lean](lean/Verification/Calculus/Values.lean) | Shared runtime values. No project imports. |
| [Types.lean](lean/Verification/Calculus/Types.lean) | Type syntax and its meaning as sets of values. |
| [Programs.lean](lean/Verification/Calculus/Programs.lean) | Core calculus program syntax and execution semantics. |
| [SourceAst.lean](lean/Verification/SourceAst.lean) | TypeScript source AST with locations. |
| [Lowering.lean](lean/Verification/Lowering.lean) | Source AST → core calculus translation. Start at `eraseProg`. |
| [TypeOperations.lean](lean/Verification/Calculus/TypeOperations.lean) | Type constructors, comparisons, intersection and difference, with correctness proofs. |
| [Narrowing.lean](lean/Verification/Calculus/Narrowing.lean) | Type environments, branch refinement and its correctness proofs. |
| [Typing.lean](lean/Verification/Calculus/Typing.lean) | Typing rules and program soundness. |
| [Checker.lean](lean/Verification/Calculus/Checker.lean) | Standalone type checker and its correctness proof. |
| [Calculus.lean](lean/Verification/Calculus.lean) | Import-only entry point for the calculus modules. |
| [Obligation.lean](lean/Verification/Obligation.lean) | The relations to establish, their meaning, and a proved discharge procedure. |
| [Verify.lean](lean/Verification/Verify.lean) | Traverse the source program, generate and discharge obligations, and prove acceptance implies typing. |
| [SkjsTypeClaims.lean](lean/Verification/SkjsTypeClaims.lean) | The claim format, claim lookup and signature input validation. |
| [JsonDecode.lean](lean/Verification/JsonDecode.lean) | JSON decoding. |
| [Tests/](lean/Verification/Tests) | One test file per calculus module, named after it; each header says what it pins. Built with the verifier. |
| [SkjsTypeClaims.sk](../src/SkjsTypeClaims.sk) | Emit SKJS's claims: expression types, statement environments and function signatures. |
| [run.sh](run.sh) | Build when requested, run the corpus and claim validation tests, and report results. |
