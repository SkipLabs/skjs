# Independent claim verification

This pipeline checks supplied types and program-point invariants against an
independent calculus. SKJS is one claim producer; producer-independent candidates
use the same source adapter and independently checked certificates. We do not
assume SKJS or proof search is sound.

There is one maintained calculus and verifier. Its implementation lives in
`lean/Verification/ExperimentState/` (the directory name is historical).
[DESIGN.md](DESIGN.md) describes the architecture and trust boundary.

The base language everything else is defined over is small, and stated in two
places. [Terms and values](SEMANTICS.md#operational-language) are the programs
the indexed model interprets directly; [formulas and clauses](POSITIVE-TYPES.md#representation-and-mathematical-rules)
are the types a graph label can name. [Control-flow graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)
and [state assertions](POSITIVE-TYPES.md#state-assertion-grammar) are layered on
those two rather than alternatives to them.

The supported source profile includes null, undefined, Boolean and numeric unions, required
cell fields, and callbacks with ordered required parameters. The
[undefined examples](tests/stateful-source/undefined.ts) exercise contracts, alias
writes, strict comparisons and nullish coalescing. This does not imply support
for `void`, optional properties or implicit returns; see the
[current fragment](DESIGN.md#source-integration-current-slice-and-next-milestone).

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
- `make verify-examples` builds Lean and checks fresh SKJS and tsc claims for the
  viewer's example corpus. Each function has a producer-to-proof pair, for example
  `SKJS ✓→✓ · tsc ✓→✗`. Proof `✓` means independently verified, `✗` means proof
  search failed (not a disproof), and `?` means unsupported source or missing claims.
  `⚠` highlights SKJS acceptance not established by its claims; it is not itself
  evidence of an SKJS bug.
  No repair is applied; repair demonstrations belong to the regression suites.
- `make verify-census` measures original SKJS repair regressions against a separate
  baseline. See [Repair coverage](REPAIR-COVERAGE.md) for the denominator,
  inspected blockers and continuation workflow.
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
node verification/examples.mts
node verification/examples.mts --skjs target/host/dev/skjs.some-variant
```

Rebuild SKJS when its implementation changes. Repository-wide `make test` checks
SKJS itself; it is not required for changes confined to the verifier or reports.

## Current source fragment

The source adapter supports **functions with primitive or bounded callable
parameters, initialized `const` bindings, nested branches, `while` loops with `break`/`continue`, and
returns**, where a `const` or `let` statement may declare several bindings,
bound left to right under the statement's one entry, and a `const` may bind an
object pattern of identifier properties with optional defaults over a local
record, over local cells and bounded expression closures and calls. Cell
fields, arrow arguments and arrow results admit primitive and recursively
callable contracts; nested record operands remain excluded. Annotations may union the supported primitive, cell and
function types with ordered required parameters. Creating and invoking closures
preserves parameter order and requires an exact argument count, including zero. Immutable Boolean, null and undefined tests refine what
follows them, including through `&&`, `||`, `??`, `?:` and negation.
Strict `typeof e === "function"` and `!==` tests evaluate the operand once;
tests on immutable variables retain only the corresponding callable alternatives. Every path must reach an explicit return.

Nullish assignment to mutable locals and parameters (`x ??= rhs`) is supported.
Its lowering lives in Lean and checks both the skipped and writing paths, using
the existing heap and nullish-test rules. [nullish-assignment.ts](tests/stateful-source/nullish-assignment.ts)
covers skipped RHS effects, nested assignments and escaping callbacks with both
producers. Property assignment targets remain outside this form.

A fresh arrow can acquire one initialized mutable `value` field using explicitly
typed `Object.assign`; aliases preserve both the field invariant and call signature.
See [function-field.ts](tests/callables/function-field.ts). Known local arrows and
their immutable aliases support `.call(receiver, ...actuals)`: the receiver is
evaluated before the actuals, then discarded. Arbitrary callable parameters and
receiver-dependent methods remain excluded. `.bind` on the same local arrows
saves a required argument prefix and returns a closure over the remaining
parameters, including a thunk when all parameters are bound. SKJS rejects this
partial binding; the [incompleteness example](tests/skjs-incomplete/bound-arguments.ts)
verifies using TypeScript’s claims.

Loops inside closures, external cell parameters, labeled transfers,
active-name shadowing, other `typeof` comparisons, general strings, and overloads
are outside it. An initialized `let` is in it: it allocates a private
cell the source never sees as a value, reading the name reads the cell,
assignment writes it and yields the value written, and a closure holds the
cell's identity, so it observes later writes. The annotation is the storage
contract every assignment is checked against when one is written. Current-content claims are checked
as read obligations or primitive heap observations; immutable snapshots can keep
precise contents across later writes. Guard refinement of mutable contents is
still conservative. A `let` may omit its annotation: the producer states the
contract for a binding it inferred, the type it gives the name where it first
stands in scope, and that is checked like a written one rather than the
initializer's type being taken for it. A `let` without an initializer is
outside. Numbers can be bound, passed, returned, held in a union and shape-tested.
Strict comparisons against numeric singletons also verify for finite unions
with known comparison outcomes; arithmetic is outside the fragment. A numeric
literal is its own singleton and is below `number`; its identity is the double
it denotes, so `1`, `1.0` and `1e0` are one literal. A number may be a
parameter or result of a closure, and the storage contract of a mutable local,
so a captured reader of a numeric `let` verifies. Numeric current-content assertions are supported on incoming edges, including
numeric contents of local cells; a broad `number` assertion does not establish a
particular singleton. Generic variable-copy bodies admit distinct type parameters and bounds to
`boolean` or an earlier parameter, including transitive chains. Parameters,
annotated `const` copies and results use those rigid types or `boolean`;
conversions follow declared bounds only. Dependent parameters retain their rigid identity in raw SKJS exports. First-order aliases
`type Id<T> = T` and `type Box<T> = { value: T }` remain single-parameter.
Generic callbacks, call-site instantiation and other generic bodies remain outside.
The fragment is smaller than the calculus,
and the parser can represent syntax the Lean adapter then rejects: such a
rejection is a limitation, never evidence that a producer claim is false.

[Design](DESIGN.md#source-integration-current-slice-and-next-milestone) owns what
is accepted and why, together with the gates and the loop, closure and
continuation constructions; [the protocol](REQUEST-PROTOCOL.md#source-mode) owns
the source-mode commands, the type and claim encodings, and their exact
restrictions. Worked examples of each construct live in
[the corpus](tests/README.md), including the [Callables coverage map](tests/callables/README.md)
and [producer counterexamples](tests/skjs-unsound/README.md).

## Reports and examples

Start the local viewer with:

```sh
node verification/report-viewer/serve.mts
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
| [REPAIR-COVERAGE](REPAIR-COVERAGE.md) | Repair measurement, continuation checkpoint, inspected blockers and safe extension workflow. |
| [DESIGN](DESIGN.md) | Architecture, trust boundary, decisions, corpus-led priorities and integration status. |
| [SEMANTICS](SEMANTICS.md) | The term and value grammar, execution, worlds, heap satisfaction, membership and safety predicates. |
| [POSITIVE-TYPES](POSITIVE-TYPES.md) | Type and state-assertion grammars, normalization, declarative subtyping and subtype certificates. |
| [PROGRAM-TYPING](PROGRAM-TYPING.md) | The graph program syntax, program/graph rules and their mathematics, side conditions, soundness, derived forms and evidence construction. Semantic rules awaiting integration are marked separately. |
| [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) | Calculus request/evidence JSON, verifier CLI, and SKJS source AST/export encoding. |
| [SOURCE-CLAIMS](SOURCE-CLAIMS.md) | Implemented independent sidecar schemas, conversion, source identity and repair workflow. |
| [CLAIM-INTERFACE](CLAIM-INTERFACE.md) | Explicitly unimplemented arbitrary-graph and comment-input proposals; links to implemented subsets. |
| [LANGUAGES](LANGUAGES.md) | Every representation data crosses, which file owns each on both sides, the naming convention, and where it does not hold. |
| [ANNOTATED-SOURCE](ANNOTATED-SOURCE.md) | Report output, manifest, annotations, provenance and freshness. |
| [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md) | Failure records, source maps, outcome classification and reason vocabulary. |
| [Viewer README](report-viewer/README.md) | Viewer/editor UX, local server, implementation structure and browser integration. |
| [Test index](tests/README.md) and linked corpus READMEs | Regression coverage, runnable witnesses, producer/runtime outcomes and exact candidate repairs. |

When adding a rule, put its mathematical statement and proof scope in
`PROGRAM-TYPING` (or `POSITIVE-TYPES` for subtyping). New semantic predicates go
in `SEMANTICS`; wire fields go in the relevant protocol document. Update `DESIGN`
with the decision and remaining integration, not a second rule specification.
Keep corpus mechanics with the examples. Distinguish **exportable**, **proved in
the model**, and **accepted by the source checker** wherever those statuses differ.
Avoid temporary paths, task handoffs and duplicate field tables in maintained
docs. Lean definitions and tests remain the implementation evidence; cite them.

The source boundary starts in
[Fragment.lean](lean/Verification/ExperimentState/Fragment.lean) and
[SourceExtraction.lean](lean/Verification/ExperimentState/SourceExtraction.lean);
[RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean) checks the
resulting requests and evidence.

`tools/export-source-claims.mts` converts an existing SKJS export into editable
calculus-label claims. Conversion records unsupported candidates and provenance;
it does not itself establish verification. Sidecars also preserve
current-content assertions such as `{ value: boolean = (true) }`, separately from
the storage invariant. Supplied observations are checked obligations: every
incoming edge, including loop backedges, must establish the assertions claimed at
a statement entry. See
[Current-content assertions](DESIGN.md#current-content-assertions).
