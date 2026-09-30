# Independent claim verification

This pipeline checks supplied types and program-point invariants against an
independent calculus. A producer proposes the claims: the OCaml producer, or
TypeScript's own checker for the corpus. Every producer's claims go through the
same source adapter and independently checked certificates. Neither a producer
nor proof search is assumed sound.

There is one maintained calculus and verifier. Its implementation lives in
`lean/Verification/Model/`, organized by semantics, types, program rules,
source integration, and tests. Declarations share the `Verification.Model`
namespace; module paths identify their topic. These folders aid navigation,
not an enforced dependency order: some derived semantic lemmas depend on
program rules.
[DESIGN.md](DESIGN.md) describes the architecture and trust surface;
[REFERENCES.md](REFERENCES.md) collects the works it draws on.

The base language everything else is defined over is small, and stated in two
places. [Terms and values](SEMANTICS.md#operational-language) are the programs
the indexed model interprets directly; [formulas and clauses](POSITIVE-TYPES.md#types-and-clauses)
are the types a graph label can name. [Control-flow graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)
and [state assertions](POSITIVE-TYPES.md#state-assertion-grammar) are layered on
those two rather than alternatives to them.

The TypeScript the pipeline reads is summarised under
[current source fragment](#current-source-fragment); the
[fragment boundary](DESIGN.md#fragment-boundary) lists what it refuses and why.

## Run

Prerequisites: Node, the pinned [Lean toolchain](lean/lean-toolchain), OCaml
and Dune ([the producer guide](ocaml-producer/README.md#try-it)). Install the
tools once:

```sh
(cd verification/tools && npm install)
npm ci --prefix verification/ocaml-producer/upstream   # the fixture's @types/node
make verify
```

Tests favour end-to-end pipeline cases, source files through the parser, the
OCaml producer and Lean, over unit tests of intermediate steps; tests written
while researching a feature retire once a pipeline case covers it
([AGENTS.md](AGENTS.md#which-tests-to-keep)).

The commands separate regression testing from inspecting example outcomes:

- `make verify-test` builds Lean and runs the pipeline's suites: the OCaml
  producer's cases, front-end types, JSON field names, documents, the rule
  inventory and the source boundaries. Its summary counts test executables,
  not functions or assertions, and marks an incomplete run after an early
  failure.
- `make verify-examples` builds Lean and checks TypeScript's own claims for
  the viewer's example corpus ([tsc claims](tests/tsc-claims/README.md)).
  Each function shows TypeScript's verdict and whether the verifier derives
  its claims: proof `✓` means independently verified, `✗` means proof search
  failed (not a disproof), and `·` means no claim was stated.
- `make verify` runs both, building Lean once and keeping their summaries separate.

Terminal output uses green for success, red for rejection or failed proof search,
and amber for unavailable checks. Symbols and words remain visible without
color. Redirected output, `TERM=dumb`, and a nonempty `NO_COLOR` disable
colors. Use `VERBOSE=1` for build details and example diagnostics. Without
rebuilding Lean:

```sh
verification/run.sh
node verification/examples.mts
```

## Current source fragment

A source file is a module, checked per code unit: each function, and the
module's initialization, which runs its constants, classes, enums and
top-level statements ([modules and code units](DESIGN.md#modules-and-code-units)).
In outline, the parser admits:

- **Statements**: `const` and `let` bindings, annotated or not (a `let`
  nothing writes is a `const`); object and array patterns with defaults,
  holes and rests; `if`, `switch`, `while`, `for`, `for...of` over arrays,
  `for...in`, labeled blocks, `break` and `continue`; `throw` and
  `try`/`catch`/`finally`, a throw being an outcome
  ([statement forms](PROGRAM-TYPING.md#statement-forms),
  [patterns](PROGRAM-TYPING.md#patterns), [throws](DESIGN.md#throws)).
- **Values and operators**: `null`, `undefined`, Booleans, numbers, bigints,
  strings and symbols, with literal types; arithmetic, relational comparison
  of operands in their primitive order, string `+` and template literals,
  compound and logical assignment; `typeof`, `in`, `instanceof`,
  truthiness, strict equality and `== null` as guards
  ([values](DESIGN.md#values), [guards](DESIGN.md#guards)).
- **Objects and arrays**: object literals with spreads, records, index
  signatures, dense arrays and tuples, optional chaining, enums, and classes
  with fields, methods, statics, parameter properties and a base class of the
  file ([objects and prototypes](DESIGN.md#objects-and-prototypes),
  [classes](PROGRAM-TYPING.md#classes)).
- **Functions**: declarations, function expressions and arrows with
  optional, default and rest parameters, closures as graph code, method
  members host-relative, `.call`, `.apply` and `.bind`; generic functions and
  classes certified at every instantiation; `async` functions and `await`
  of promises of primitives ([calls](DESIGN.md#calls),
  [generic bodies](DESIGN.md#generic-bodies),
  [async and iteration](DESIGN.md#async-and-iteration)).
- **Types**: what TypeScript's declarations state, read by the declaration
  reader: aliases, interfaces, unions, intersections, computed types and
  library types through reviewed overlays; imports, ambient declarations and
  globals are assumptions at their declared types
  ([trust surface](DESIGN.md#trust-surface)).

A type assertion (`e as T`, `e satisfies T`, `e!`) decides nothing: `T` is one
more type the operand must meet, so an assertion never establishes what a
guard would.

Everything else is refused with a located reason. The fragment is smaller
than the calculus, and the parser can represent syntax the Lean adapter then
rejects: such a rejection is a limitation, never evidence that a producer
claim is false. How much of SKJS's own test suite this covers, and what stops
the rest, is measured in [SKJS-COVERAGE](ocaml-producer/SKJS-COVERAGE.md).

[Design](DESIGN.md#fragment-boundary) owns what
is refused and why, and [PROGRAM-TYPING](PROGRAM-TYPING.md#reading-the-source)
how the source is read; [the protocol](REQUEST-PROTOCOL.md#source-mode) owns
the source-mode commands, the type and claim encodings, and their exact
restrictions. Worked examples of each construct live in
[the corpus](tests/README.md), including the [Callables coverage map](tests/callables/README.md). The
[callable surface](tests/callables/README.md#the-callable-surface) states which
TypeScript callable forms are supported, where each unsupported one stops, and
the order in which they are to be taken.

## Reports and examples

Start the local viewer with:

```sh
node verification/report-viewer/serve.mts
```

Open the printed URL. The groups hold the corpus examples, the OCaml
producer's fixtures and explicitly unsupported examples. Arbitrary repository source can be selected with `?file=relative/path.ts`.
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
| [DESIGN](DESIGN.md) | Principles, architecture, the model in brief, the trust surface, the fragment boundary, lasting decisions and next steps. |
| [SEMANTICS](SEMANTICS.md) | The term and value grammar, execution, worlds, heap satisfaction, membership and safety predicates. |
| [POSITIVE-TYPES](POSITIVE-TYPES.md) | Type and state-assertion grammars, normalization, declarative subtyping and subtype certificates. |
| [RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md) | Generic declarations as parameterized equations: labels, unfolding, substitution, family subtyping, lowering, wire format and acceptance statement. |
| [PROGRAM-TYPING](PROGRAM-TYPING.md) | The graph program syntax, program/graph rules and their mathematics, side conditions, soundness, derived forms and evidence construction. |
| [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) | Request/evidence JSON, the verifier CLI, and the source AST encoding. |
| [SOURCE-CLAIMS](SOURCE-CLAIMS.md) | The independent sidecar schemas and source identity. |
| [LANGUAGES](LANGUAGES.md) | Every representation data crosses, which file owns each on both sides, the naming convention, and where it does not hold. |
| [ANNOTATED-SOURCE](ANNOTATED-SOURCE.md) | Report output, manifest, annotations, provenance and freshness. |
| [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md) | Failure records, source maps, outcome classification and reason vocabulary. |
| [VIEWER-LANGUAGE](VIEWER-LANGUAGE.md) | The viewer's claim language and its boundaries: what it displays and its two typed representations. |
| [Viewer README](report-viewer/README.md) | The claim report reader, display-only: its use, local server, implementation structure and browser integration. |
| [Test index](tests/README.md) and linked corpus READMEs | Regression coverage, the corpus and its runnable witnesses. |
| [REFERENCES](REFERENCES.md) | Every cited paper, specification, tool and issue, with what the project uses from it and where. Other documents link to its anchors. |
| [TRUST-REDUCTION](TRUST-REDUCTION.md) | The bridges between source and theorem that rest on review, the options for narrowing or proving each, and host lemmas against a mechanized ECMA-262. |

When adding a rule, put its mathematical statement and proof scope in
`PROGRAM-TYPING` (or `POSITIVE-TYPES` for subtyping). New semantic predicates go
in `SEMANTICS`; wire fields go in the relevant protocol document. Update `DESIGN`
with the decision and remaining integration, not a second rule specification.
Keep corpus mechanics with the examples. Distinguish **exportable**, **proved in
the model**, and **accepted by the source checker** wherever those statuses differ.
Avoid temporary paths, task handoffs and duplicate field tables in maintained
docs. Lean definitions and tests remain the implementation evidence; cite them.

What a change must carry depends on the layer it touches. A new typing or
subtyping rule needs its soundness lemma in the model and a `#print axioms`
line. A new lowering or adapter case needs no lemma, but it must emit its
checks as located obligations (never a bare string), reuse an existing rule
rather than add an approximate one, and come with a positive witness, an
independent negative control and a tampering test; see the
[test index](tests/README.md). A new wire field needs its decoder, every
producer and consumer updated together, and a tampering test for the field.
A compilation of one form into existing rules needs a statement of what
justifies it — the compiled derivations are consequences, never the reason for
acceptance — and one interface so a later certificate can replace it.

The source boundary starts in
[Fragment.lean](lean/Verification/Model/Source/Fragment.lean) and
[SourceExtraction.lean](lean/Verification/Model/Source/SourceExtraction.lean);
[RequestJson.lean](lean/Verification/Model/Source/RequestJson.lean) checks the
resulting requests and evidence.

The main Lean entry points are:

| Area | Entry points |
| --- | --- |
| Operational semantics and worlds | [Calculus](lean/Verification/Model/Semantics/Calculus.lean), [Worlds](lean/Verification/Model/Semantics/Worlds.lean), [ObjectCoherence](lean/Verification/Model/Semantics/ObjectCoherence.lean) |
| Semantic families and graph types | [Types](lean/Verification/Model/Types/Types.lean), [PositiveGraphs](lean/Verification/Model/Types/PositiveGraphs.lean), [PositiveRules](lean/Verification/Model/Types/PositiveRules.lean) |
| Program typing and checked evidence | [ProgramTyping](lean/Verification/Model/Programs/ProgramTyping.lean), [ProgramCertificates](lean/Verification/Model/Programs/ProgramCertificates.lean), [CertificateProducer](lean/Verification/Model/Programs/CertificateProducer.lean) |
| Source boundary and CLI | [Fragment](lean/Verification/Model/Source/Fragment.lean), [SourceExtraction](lean/Verification/Model/Source/SourceExtraction.lean), [SourceClaimJson](lean/Verification/Model/Source/SourceClaimJson.lean), [RequestCli](lean/Verification/Model/Source/RequestCli.lean) |
| Other code and tests | [OCaml producer](ocaml-producer/README.md), [Node tools](tools/), [report viewer](report-viewer/README.md), [regression index](tests/README.md) |

Sidecars preserve current-content assertions such as
`{ value: boolean = (true) }`, separately from the storage invariant. Supplied
observations are checked obligations: every incoming edge, including loop
backedges, must establish the assertions claimed at a statement entry. See
[Current-content assertions](DESIGN.md#current-content-assertions).
