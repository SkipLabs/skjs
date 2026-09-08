# Independent claim verification

This pipeline checks supplied types and program-point invariants against an
independent calculus. SKJS is one claim producer; producer-independent candidates
use the same source adapter and independently checked certificates. We do not
assume SKJS or proof search is sound.

There is one maintained calculus and verifier. Its implementation lives in
`lean/Verification/ExperimentState/` (the directory name is historical).
[DESIGN.md](DESIGN.md) describes the architecture and trust boundary.
The [handoff note](HANDOFF.md) records the consolidation checkpoint and deferred items.

## Run

Prerequisites: Node, the pinned [Lean toolchain](lean/lean-toolchain), and Docker
(or a devcontainer). Install tools and build SKJS once:

```sh
(cd verification/tools && npm install)
make build-in-docker
make verify
```

The commands separate regression testing from inspecting example outcomes:

- `make verify-test` builds Lean and runs named pipeline suites: source integration,
  altered claims and certificates, source boundaries, partial exports and report/editor
  tests. Its summary counts test executables, not functions or assertions, and marks
  an incomplete run after an early failure.
- `make verify-examples` builds Lean and checks fresh, original SKJS claims for the
  viewer's example corpus. It lists each function with the viewer's paired outcomes:
  `SKJS ✓/✗/· · proof ✓/✗/?`. Proof `✓` means independently verified, `✗` means proof
  search failed (not a disproof), and `?` means unsupported source or missing claims.
  `⚠ outcomes differ` calls attention to disagreement without claiming an SKJS bug.
  No repair is applied; repair demonstrations belong to the regression suites.
- `make verify` runs both, building Lean once and keeping their summaries separate.

The example summary counts functions by producer and proof outcome. A separate
expectation check fails the command on unexpected verification outcomes or runner
errors. Matching expectations does not mean every example verifies. Both commands
use some of the same source fixtures, for these different purposes.
Terminal output uses green for success, red for rejection or failed proof search,
and amber for unavailable checks or differing outcomes. Symbols and words remain
visible without color. Redirected output, `TERM=dumb`, and a nonempty `NO_COLOR`
disable colors.
Use `VERBOSE=1` for build details and example diagnostics. Without rebuilding Lean:

```sh
verification/run.sh
verification/run.sh --skjs target/host/dev/skjs.some-variant
node verification/examples.js
node verification/examples.js --skjs target/host/dev/skjs.some-variant
```

Rebuild SKJS when its implementation changes. Repository-wide `make test` checks
SKJS itself; it is not required for changes confined to the verifier or reports.

## Current source fragment

The source adapter supports **functions with primitive parameters, initialized `const`
bindings, nested branches, `while` loops and returns**, local cells, and bounded expression
closures and calls. Both falling-through arms share one continuation.
Boolean singleton claims are translated exactly, including refinements from
direct or negated Boolean variable tests. Active-name shadowing remains gated. See the protocol's source-mode
commands and limitations. Boolean `!` evaluates its operand once; singleton results are checked using
the proved `ifKnown` rule. Closures have one null/Boolean primitive argument and a
primitive result; expression bodies compose literals, variables, cell operations
and calls. Straight-line blocks support local consts, effects and a final return,
with checked statement environments.
Every internal claim has a separately checked typing proof. Top-level function
bodies support block-bodied `while`, including nesting and early returns. Supplied
head invariants are checked on entry and every back edge; conditions are evaluated
anew. Unlabeled `break` and `continue` use checked scope-dropping transfers to
the nearest loop exit or head. Mutable variable bindings, loops inside closures,
labeled transfers and general partially returning nested closure arms remain gated.
Terminal closure `if/else` blocks are supported, with both arms returning and
checked singleton refinement of directly tested immutable Boolean variables.
Branches whose two arms fall through share one continuation using ordinary let
composition; arm-local bindings and refinements do not escape the join.
Early-return tests also work when one arm returns on every path and the other
contains no returns. Only the surviving path executes the continuation, with
its checked Boolean refinement and without the falling arm's local bindings.


Strict `===` and `!==` comparisons with a null literal work as expressions,
including inside callbacks. In top-level branches and loops, direct immutable
variable tests also refine the outgoing environment, including negations and
either operand order. `stateful-source/null-guards.ts` illustrates guarded returns,
older-slot mappings, loop bodies and break. The separate
`skjs-incomplete/null-loop-exit.ts` demonstrates independently verifiable repaired
loop-exit claims after a null test and `continue`.

The source fragment is smaller than the calculus. General strings/numbers,
`typeof`, other equality tests, mutable bindings, generics and general overloads
are not currently source-verifiable. Null-based environment refinement inside
closures and retained refinement of property reads remain unsupported. The parser
can represent some syntax that the Lean adapter subsequently rejects. Such
rejection is a limitation, not evidence that a producer claim is false.

## Reports and examples

Start the local viewer with:

```sh
node verification/report-viewer/serve.js
```

Open the printed URL. The default group contains current-verifier examples.
Separate groups contain claim-repair exercises, SKJS unsoundness examples, SKJS incompleteness examples, and
explicitly unsupported examples. Arbitrary repository source can be selected with `?file=relative/path.ts`.
See the [reader guide](report-viewer/README.md) and
[annotated report format](ANNOTATED-SOURCE.md).

## What is established

1. An independent TypeScript parser emits source syntax and positions.
2. A producer supplies candidate types and environments.
3. Lean reconstructs a calculus request, including source annotation obligations.
4. Proof search proposes evidence; the independent consumer checks it against
   that exact request. Acceptance implies typing and modeled execution safety.

Termination is not guaranteed. Applying the safety result to JavaScript still
requires trust in source parsing, extraction, the semantic definitions and Lean's
execution infrastructure. Source extraction is reviewed, not proved equivalent
to JavaScript. Accepted functions do not certify every unused displayed claim.

## Code and proof guides

| Location | Responsibility |
|---|---|
| [SourceEncoding.lean](lean/Verification/ExperimentState/SourceEncoding.lean) | Primitive wire data and JSON helpers; accepted encodings have exact-translation lemmas. |
| [SourceInput.lean](lean/Verification/ExperimentState/SourceInput.lean) | Decoded source AST and claims. |
| [SourceExtraction.lean](lean/Verification/ExperimentState/SourceExtraction.lean) | Compile source into graph nodes, point claims and closure obligations. |
| [RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean) | Produce and independently check exact requests and evidence. |
| [SEMANTICS.md](SEMANTICS.md) | Values, execution, worlds and safety. |
| [POSITIVE-TYPES.md](POSITIVE-TYPES.md) | Type normalization, declarative rules and certificates. |
| [PROGRAM-TYPING.md](PROGRAM-TYPING.md) | Program typing rules and soundness. |
| [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md) | Graph and source verification commands. |
| [SOURCE-CLAIMS.md](SOURCE-CLAIMS.md) | Producer-independent editable source claims and export. |
| [tests/README.md](tests/README.md) | Current regression coverage and explicit boundaries. |

`tools/export-source-claims.js` converts an existing SKJS export into editable
calculus-label claims. Conversion records unsupported candidates and provenance;
it does not itself establish verification.

## Primitive callbacks and a producer counterexample

[primitive-callbacks.ts](tests/stateful-source/primitive-callbacks.ts) covers
Boolean/union identity callbacks, captured writers, returned writers and a
contravariant function assignment. `stableSnapshot` shows why an immutable value
saved before a callback remains safe after the callback mutates its source cell.

[The captured-refinement example](tests/skjs-unsound/captured-refinement.ts)
is accepted by SKJS but returns false where its annotation requires true.
[Its test](tests/primitive-callbacks.js) distinguishes the original unsupported
refined-reference contract from a stale expression claim that fails proof checking
after those reference refinements are forgotten. See the
[unsoundness notes](tests/skjs-unsound/README.md).

[negation.ts](tests/stateful-source/negation.ts) adds negated conditions, closures
and loops. [The loop-exit example](tests/skjs-incomplete/negated-loop-exit.ts)
is rejected by SKJS but verifies after repairing its final binding and expression
claims to `true`. The regression consumes normal-mode partial claims and checks
the resulting certificate independently.
