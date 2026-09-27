# Working in `verification/`

An independent verifier for SKJS's type claims: a calculus with a semantic
model and soundness proofs in Lean, a checker that validates certificates, and
a pipeline that lowers a TypeScript function, has SKJS export its claims, and
asks whether they are derivable. [README.md](README.md) is the entry point;
[DESIGN.md](DESIGN.md) holds the decisions. Everything below is what an agent
needs to change things here without breaking the suite's shape.

Preserve SKJS acceptance, inference and diagnostics while doing this experiment.
Keep rejected safe programs as incompleteness findings; only behavior-preserving
claim extraction changes belong here. An explicit user request to repair SKJS
changes that task scope; keep the repair separate from pipeline extensions.
[DESIGN.md](DESIGN.md) owns the experiment boundary. Follow the root
[checker/verifier disagreement rules](../AGENTS.md#resolving-checkerverifier-disagreements):
a fixed location contract is distinct from current contents, and faithful export
must not invent a justification the checker never established. Before attributing
a refusal to an exported field, trace the actual consumer of that field.

For repair-coverage work, start with [REPAIR-COVERAGE.md](REPAIR-COVERAGE.md):
measurement, current checkpoint, inspected blockers and extension pitfalls.

## Commands

SKJS is frozen at the tag `skjs-frozen` ([DESIGN.md](DESIGN.md#skjs-is-frozen)):
work iterates on the parser → OCaml producer → Lean pipeline, and
`verification/run.sh` runs only that pipeline's suites by default. The SKJS
producer, the suites built on its fixtures and the corpus (`examples.mts`)
run only when asked, and may fail on arrays past the tag.

```sh
verification/run.sh              # the OCaml pipeline's suites (~25 s)
make verify                      # from the repo root: build, suites, then the corpus
make verify-census               # original SKJS repair functions (separate baseline)
make verify-test                 # the suites only
make verify-examples             # the corpus only
verification/run.sh --suite all  # every suite, SKJS's included, without rebuilding Lean
(cd verification/lean && lake build)  # the verifier alone
node verification/examples.mts    # the corpus alone, both producers
make verify-examples-skjs        # one column at a time; either alone runs
make verify-examples-tsc         # only that producer
make viewer                      # the claim report reader on http://localhost:8731
```

### Iterating: run what the change touches

The full battery is for deep changes. While iterating, run the narrowest tier
that covers what changed, and the wider tier once before committing:

| Changed | While iterating | Before committing |
| --- | --- | --- |
| OCaml producer (`ocaml-producer/*.ml`) | `dune build --root verification/ocaml-producer`, then `node verification/ocaml-producer/run-cases.mts <pattern>` (cases whose file names contain the pattern; about a second for a handful) | `node verification/ocaml-producer/test.mts` (all cases, pinned imports, tampering, reader: ~45 s); `dune runtest --root verification/ocaml-producer` if `unit.ml` changed |
| One source file | `node verification/ocaml-producer/check.mts <file.ts> [--project dir]` | — |
| Lean | `(cd verification/lean && lake build)`, then `run-cases.mts` for the affected cases | `verification/run.sh` |
| Parser, Fragment or SourceClaims wire, shared tools | `(cd verification/tools && npx tsc -p tsconfig.json)`, `node verification/tests/json-field-names.mts` (instant: TypeScript, Lean and OCaml use the same JSON field names), then `run-cases.mts` | `verification/run.sh` |
| Viewer | `(cd verification/report-viewer/app && npm run check)` | `test.mts` (its reader section) |

`run-cases.mts` with no pattern runs every case (~15 s) and is the first part
of `test.mts`, through the same check.

`make verify-test` includes the OCaml producer's Dune unit tests and its
end-to-end source cases, including imports from the pinned upstream source
tree. Install OCaml and Dune as described in
[the producer guide](ocaml-producer/README.md#try-it) before running it.

One file end to end, with `$F` a repository-relative path:

```sh
node verification/tools/fragment-parse.mts $F > ast.json
bash verification/skjs.sh --emit-skjs-type-claims $F > claims.json
verification/lean/.lake/build/bin/verifier --produce-stateful-source ast.json claims.json $F evidence.json 10
verification/lean/.lake/build/bin/verifier --check-skjs-operations claims.json
```

`skjs.sh` runs SKJS in the `skiplabs/skip` container; inside a devcontainer it
runs the binary directly. Never invoke `target/host/dev/skjs` yourself.

## Which tests to keep

The end-to-end pipeline cases are the primary signal: a source file through
the parser, the OCaml producer and Lean (`ocaml-producer/cases.mts`, run by
`run-cases.mts`). They exercise the unproved parts together (parser,
extraction, producer, wire), and what Lean proves needs no test.

- **Prefer a pipeline case.** A new feature's test is a source file with its
  expected outcome, positive and negative, not a unit test of an
  intermediate step.
- **Research tests are temporary.** Tests written while working a feature out
  (a Lean `#guard` on a hand-built graph, a probe of one tool) are useful
  while researching it. Once a pipeline case covers the behaviour, retire
  them in the same or the next commit.
- **Keep a test only for what the pipeline cannot show:** a refusal no source
  can reach (forged evidence, a tampered declaration), a boundary of a
  trusted input (the `ArrayProto` overlay), or a speed-critical check.
- **Remove what adds no signal.** A test a proof already covers, or one that
  repeats another's inputs through the same path, goes. Before removing a
  forged-claim test, check it does not test extraction: which program point a
  claim is attached to is unproved.

## The suite's shape, and the rules that keep it

`run.sh` keeps the suites fast through four decisions. Each is a rule for
anything added; the runner summary reports the current suite count.

- **One container for the run.** `skjs_start` brings it up before anything
  forks; `skjs_run` and `skjs_check` exec into it. A suite never starts its
  own container and never calls docker.
- **One SKJS call per batch.** `skjs check` takes many paths and names each
  file in its output, and a container exec costs more than checking a small
  file. Export several sources in one call, never in a loop.
- **Setup is backgrounded, together.** A fixture is a parsed source plus its
  claims, built by `fixture` (or `rejected_fixture` when SKJS rejecting the
  program is the point). Every build goes through `build …`, which forks it,
  and the script waits for all of them once. Setup placed after that wait is
  serial and lands on the critical path: put new setup before it, in the
  batch. Sources that must not go through the source parser, because they
  use TypeScript outside the fragment, get their own helper, as
  `snapshot_probes` does.
- **Suites start together.** A suite is `run_test "Name" command args…`; its
  output is buffered and reported in order, and a failure is counted, never
  fatal. A suite reads the fixtures the script built and runs the verifier
  binary; it does not build Lean, does not run SKJS, and does not run the
  corpus. The OCaml suite also builds its Dune executable before its tests.

`examples.mts` follows the same rules on its own: one producer run for every
corpus file, one worker per core, and colour decided once in the parent.

## What a result means

### Acceptance/soundness invariant

The verifier's successful CLI outcome must imply the modeled safety property
for every extracted function. Preserve this by construction:

- The acceptance path consumes the complete `FunctionPlan` sum through one
  exhaustive conversion to `CertifiedPlan`. It must never use `filterMap`, an
  `Option`, or a projection that can discard a plan variant.
- A new plan constructor must make that conversion fail to compile. It may
  become a certified constructor only with a checker and a theorem connecting
  its successful check to the semantic property. Until then it is a located
  gap, never `verified`.
- Keep one headline theorem, currently `SourceClaimJson.checkJson_safe`, whose
  premise is the exact CLI success condition and whose conclusion gives safety
  for every accepted function. A theorem about a retained subset, decoded
  bundle, or Boolean alone is not an acceptance soundness theorem.
- `#print axioms` checks how a theorem was proved, not whether it proves the
  required statement. Review the theorem's premise and conclusion whenever the
  accepted plan type or CLI path changes.
- Search output, direct-check success and compiled ground consequences are
  intermediate artifacts. The runner and viewer must not label them verified
  before the corresponding plan reaches `CertifiedPlan`.

- The corpus prints a pair per producer, `SKJS ✓→✓ · tsc ✓→✗`: the producer's
  own verdict on the program, then whether the verifier derives the claims it
  made. `✗` on the right means proof search found no derivation; it is never a
  disproof. `?` means the check could not be attempted. `⚠` marks an SKJS
  acceptance its own claims do not establish; the tsc column carries none,
  because exporter coverage and proof-search limits still need to be separated
  from unsoundness findings. TS now states primitive field-content assertions
  for direct reads at statement entry.
- Expected outcomes are policy, in `expectedVerified` in `examples.mts`: a
  witness fixture is expected _not_ to verify, and a run fails when any
  function's outcome contradicts the policy, in either direction.
- Fixtures under `tests/skjs-unsound/` and `tests/skjs-incomplete/` are
  findings about SKJS and carry their own comment; the group README says what
  each tool does with them. Do not "fix" one so that it verifies.
- A repair is a hand-written candidate edit kept beside the original export,
  never an automatic widening of SKJS's claims.

## Source and host soundness boundaries

The calculus theorem does not prove that a source annotation was interpreted
faithfully or that a native library meets its assumed contract. These are
separate review obligations, even when every Lean proof and suite passes.

- **Never erase an unsupported contract.** Source annotation lowering either
  represents the whole contract or refuses it. An unsupported method, a failed
  expansion, or an exhausted search/colour budget must not become `top`, lose
  a field, or lose a bound. An opaque type is not `unknown`: hiding its
  representation does not discharge its introduction obligation. The same
  declaration occurs in inputs, outputs, and invariant storage; an
  over-approximation safe for reading is not safe for producing a value.
- **Native declarations are specifications to audit, not evidence.** Review
  every callback (including implicit conversion, iteration and thenable
  callbacks, constructor lookup and `Symbol.species`), its actual arguments,
  alias mutation, and whether lengths or
  keys are captured before callbacks run. A readonly alias does not prevent
  mutation through another alias. Establish result invariants after all such
  effects; density at entry does not imply density of `map`'s result. Callback
  effects do not constrain other native entry points. Check result construction
  as well as traversal. The user-approved semantics now assumes ordinary array
  construction, also of external code: no own array `constructor`, and stable
  standard constructor/species behavior. Preserve the formal own-key exclusion
  through all array/record views and reject source operations violating it.
  Custom species are outside the admitted language; their full modeling is not
  a prerequisite for callback-effect work. Never widen this assumption silently.
- **Test the unproved boundary independently.** A producer-side refusal needs
  a verifier test bypassing that producer when annotation interpretation is
  involved. For native-contract repairs, execute the actual negative source
  fixture under Node as well as refusing it in the pipeline. This is a small
  contract counterexample, not a test of a proved Lean typing rule.
- **Keep dependencies exact.** Collect only intrinsics a source uses; do not
  load all trusted contracts because one is needed. Dependency collection may
  avoid unused declarations, but may not discard members of a collected type.
- **Coverage losses are results.** Preserve motivating sources; mark a case
  blocked by an earlier unsupported contract as a gap, not as a passing
  negative control for the later obligation. Report lost framework coverage
  explicitly. Changing an expected result requires inspecting its cause;
  passing tests after reclassification does not close the corresponding goal.

For inferred callable effects, follow the
[elaboration/certification boundary](DESIGN.md#inferred-call-effects-elaboration-and-certification).
Annotation translation must not strengthen an ordinary arrow. Producer inference
proposes a qualified signature; definition evidence must prove both safety and
the effect before application consumes it. Never recognize callback syntax at
native call sites as a substitute for that proof. Audit every signature mapping,
substitution, overload and certificate path for the effect field; exhaustive
constructor matching does not detect a discarded field. Qualified claims need
located failures and forged-evidence controls, and imported effects require an
explicit checked contract or documented external assumption.
The current effect guarantees preservation only on normal return. Do not carry
it onto a call's exceptional edge or infer preservation for a caller that catches
the exception without checking its handler against the changed heap.

The September 2026 boundary audit found two shared specification mistakes:
OCaml and Lean both treated unsupported generic methods as `unknown`, and
native array contracts copied TypeScript signatures without accounting for
reentrancy and coercion. Agreement between independent implementations did not
catch a shared mistake. Keep these mechanisms and controls when extending the
fragment; do not restore acceptance by increasing trust silently.

## Snapshots of the exporter

`tests/export-snapshots/` holds small probes with SKJS's exported claims
printed beside them. They may use any TypeScript; some supported probes are also shared with
the pipeline suites and viewer corpus. A change to what the exporter says is a diff in a `.snap` file;
read it, then regenerate:

```sh
UPDATE_EXPECT=1 node verification/tests/export-snapshots.mts claims.json verification/tests/export-snapshots
```

where `claims.json` is one `skjs_check` over the directory. Add a probe when
an exporter change needs a place to show, one phenomenon per file.

## Conventions

- Formatting: everything is prettier-formatted (`make fmt` at the root).
- The reader is a Svelte application in `report-viewer/app`, built by Vite and
  served by `report-viewer/serve.mts`. `npm run check` there is svelte-check,
  not `tsc`: `tsc` does not look inside a component's template, which is
  exactly where a wrong property name hides. `make viewer` builds and serves.
- Every module the node side runs is `.mts`, and `tools/tsconfig.json` covers
  all of them — the trusted front end, the corpus driver and the suites — under
  one fully strict configuration, `noImplicitAny` and `strictNullChecks`
  included, as well as the reader's own model and server. A new file lands in that project by being
  where it belongs; nothing is exempt.
- `tools/source-claims.mts` describes the source sidecar wire format, and
  `report-viewer/types.ts` the report the reader displays. A tool that writes
  or reads one of those documents is typed against that description rather
  than against its own idea of the shape, so producer and consumer cannot
  drift apart silently. That typing is the whole consistency mechanism: adding
  or removing a field is a compile error at every site that touches it.
- The trusted front end is TypeScript on the compiler's own API
  (`typescript/unstable/sync` for the checker, `typescript/unstable/ast` for
  the tree), type-checked by the `Front-end types` suite. A member that API
  renamed reads as `undefined` rather than failing, so `tsc` over
  `tools/tsconfig.json` is the thing that catches it — run the suite, do not
  reason about it.
- `tests/tsconfig.json` is the regime the corpus is claimed and checked under.
  The producers refuse a file no `tsconfig.json` with `"strict": true` claims,
  rather than claiming it under weaker defaults.
- node, not bun: the compiler's synchronous channel reads the child process's
  pipe through node's own `_handle`, which bun does not expose
  (`undefined is not an object (evaluating 'stdout._handle.fd')`). Every tool
  that opens the compiler is affected, so this is not a per-suite choice.
- A decoder is the only place that asserts a shape. Everything else narrows:
  a type predicate, a `typeof` before a comparison, a case table keyed by the
  language's own union. `tools/unchecked.mts` reports every written `any`, `as`
  and `!` in the node side; what it should show is one `as` at the last line of
  each decoder, where the checks it just ran become the type it returns. An
  assertion anywhere else is standing in for a check that is missing.
- Wire formats carry no version, profile or schema tag, and none is to be
  added. What a version would be for is consistency, and consistency here is a
  typing property: each format is one declared type, every producer and
  consumer is typed against that type, and every decoder requires the shape
  field by field and rejects an unknown field. So a document either has exactly
  the current shape or it is refused, and there is nothing for a tag to
  disambiguate. A `sha256` field, where present and checked, can state source
  staleness precisely; the declaration document carries no such hash and
  instead relies on TypeScript's project and source trees.
- A format is never frozen and never has two accepted shapes. Fix its shape in
  place, then regenerate the fixtures that carry it. Do not add a compatibility
  shim, a second decoder, or a field that records which shape a document is:
  every producer and consumer of these documents is in this repository, nothing
  outside reads them, and there is no older document to keep working.
- Lean: no `sorry`, no project axioms; `#print axioms` on every soundness
  theorem stays in the file. Build only the module you changed while
  iterating (`lake build Verification.Model.<Layer>.<Module>` from `verification/lean`).
  Run Lake from that directory so elan selects its pinned `lean-toolchain`;
  `lake -d` from the repository root can select a different compiler before
  changing directories. Never run simultaneous builds against the same cache.
- New executable fields on an existing AST constructor need an explicit audit
  of every lowering and certification path. Exhaustive constructor matching
  alone cannot detect a discarded field. Each path must check the field's
  execution or refuse it with a located diagnostic. In particular, a lambda
  body certificate does not cover parameter-default execution. Lowering tests
  must exercise source evaluation order and binding scope, including forged
  producer claims against both evidence production and consumption; calculus
  safety alone does not prove correspondence with JavaScript execution.
- Docs: a doc-only change needs no suite run; check anchors and prose. Cite
  papers, specifications and issues by a link to an entry of
  [REFERENCES.md](REFERENCES.md), adding the entry there.
