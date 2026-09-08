# Independent claim verification

This pipeline checks supplied types and program-point invariants against an
independent calculus. SKJS is one claim producer; producer-independent candidates
use the same source adapter and independently checked certificates. We do not
assume SKJS or proof search is sound.

There is one maintained calculus and verifier. Its implementation lives in
`lean/Verification/ExperimentState/` (the directory name is historical).
[DESIGN.md](DESIGN.md) describes the architecture and trust boundary.

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
older-slot mappings, loop bodies and break. Null guards also refine nullable
parameters and captured immutable values in supported closure branches, including
negation and effects in the selected arm. The separate
`skjs-incomplete/null-loop-exit.ts` demonstrates independently verifiable repaired
loop-exit claims after a null test and `continue`.

Conditional expressions (`c ? a : b`) use the same checked Boolean and null
refinements, including inside closures. Their result, condition and both arms
require expression claims. Only the selected arm executes; conditions may have
effects. The null-guard examples dynamically select nullable cells and callbacks
and then read or call them after a guard.

Short-circuit `a && b` and `a || b` require Boolean left operands, evaluate the
right only when selected, and preserve all operand/result claim obligations.
Immutable Boolean/null guards can refine the right operand and statement
successors. This adds neither general JavaScript truthiness nor retained property
facts; [Program typing](PROGRAM-TYPING.md#derived-source-forms) gives the rules.

Null coalescing (`a ?? b`) evaluates and saves `a` once, selecting `b` only for
null. In particular, false is preserved. It works with supported primitive, cell
and function unions, inside closures too. An immutable variable on the left is
refined to null in the fallback; property reads receive no retained refinement.
Both operand claims remain required. Undefined is outside the source profile.
Named, explicitly typed cell/callback fallbacks avoid compound inferred claims
that the current SKJS exporter cannot yet represent.

Source annotations and claims can also form unions of the supported primitive,
cell and unary function types, such as nullable local cells and optional function
results. Every arm keeps its existing validation; unsupported arms are rejected.
Cell fields and arrow inputs/results remain primitive. External cell/function
parameters remain gated: structural annotations do not establish their runtime
origin or behavior. The examples use locally allocated cells and checked closures.

The source fragment is smaller than the calculus. General strings/numbers,
`typeof`, other equality tests, mutable bindings, generics and general overloads
are not currently source-verifiable. Retained refinement of property reads
remains unsupported. The parser
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

## Documentation ownership

Each document owns one layer. Keep definitions and detailed examples in that
owner; other documents link to them and give only the context their readers need.

| Document | Owns |
| --- | --- |
| This README | Commands, a concise supported-fragment overview, and navigation. |
| [DESIGN](DESIGN.md) | Architecture, trust boundary, decisions, corpus-led priorities and integration status. |
| [SEMANTICS](SEMANTICS.md) | Values, execution, worlds, heap satisfaction, membership and safety predicates. |
| [POSITIVE-TYPES](POSITIVE-TYPES.md) | Type and state-assertion grammars, normalization, declarative subtyping and subtype certificates. |
| [PROGRAM-TYPING](PROGRAM-TYPING.md) | Program/graph rules and their mathematics, side conditions, soundness, derived forms and evidence construction. Semantic rules awaiting integration are marked separately. |
| [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) | Calculus request/evidence JSON, verifier CLI, and SKJS source AST/export encoding. |
| [SOURCE-CLAIMS](SOURCE-CLAIMS.md) | Implemented independent sidecar schemas, conversion, source identity and repair workflow. |
| [CLAIM-INTERFACE](CLAIM-INTERFACE.md) | Explicitly unimplemented arbitrary-graph and comment-input proposals; links to implemented subsets. |
| [ANNOTATED-SOURCE](ANNOTATED-SOURCE.md) | Report output, manifest, annotations, provenance and freshness. |
| [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md) | Failure records, source locations, outcome classification and reason vocabulary. |
| [Viewer README](report-viewer/README.md) | Viewer/editor UX, local server, implementation structure and browser integration. |
| [Test index](tests/README.md) and linked corpus READMEs | Regression coverage, runnable witnesses, producer/runtime outcomes and exact candidate repairs. |

When adding a rule, put its mathematical statement and proof scope in
`PROGRAM-TYPING` (or `POSITIVE-TYPES` for subtyping). New semantic predicates go
in `SEMANTICS`; wire fields go in the relevant protocol document. Update `DESIGN`
with the decision and remaining integration, not a second rule specification.
Keep corpus mechanics with the examples. Distinguish **exportable**, **proved in
the model**, and **accepted by the source checker** wherever those statuses differ.
Avoid temporary paths, task handoffs and duplicate version tables in maintained
docs. Lean definitions and tests remain the implementation evidence; cite them.

The source boundary starts in
[SourceInput.lean](lean/Verification/ExperimentState/SourceInput.lean) and
[SourceExtraction.lean](lean/Verification/ExperimentState/SourceExtraction.lean);
[RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean) checks the
resulting requests and evidence.

`tools/export-source-claims.js` converts an existing SKJS export into editable
calculus-label claims. Conversion records unsupported candidates and provenance;
it does not itself establish verification. Version-2 sidecars also preserve
current-content assertions such as `{ value: boolean = (true) }`, separately from
the storage invariant. They can be exported and displayed; required observations
remain gated until graph certificates carry heap facts. See
[Current-content assertions](DESIGN.md#current-content-assertions).

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
[The compound-write example](tests/skjs-unsound/compound-write-refinement.ts)
exercises known stale-field refinement after a direct write. Its runtime evidence,
original claim boundary and explicit diagnostic candidate are recorded in the
[unsoundness notes](tests/skjs-unsound/README.md).

[negation.ts](tests/stateful-source/negation.ts) adds negated conditions, closures
and loops. [The loop-exit example](tests/skjs-incomplete/negated-loop-exit.ts)
is rejected by SKJS but verifies after repairing its final binding and expression
claims to `true`. The regression consumes normal-mode partial claims and checks
the resulting certificate independently.
