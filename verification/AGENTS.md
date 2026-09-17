# Working in `verification/`

An independent verifier for SKJS's type claims: a calculus with a semantic
model and soundness proofs in Lean, a checker that validates certificates, and
a pipeline that lowers a TypeScript function, has SKJS export its claims, and
asks whether they are derivable. [README.md](README.md) is the entry point;
[DESIGN.md](DESIGN.md) holds the decisions. Everything below is what an agent
needs to change things here without breaking the suite's shape.

Preserve SKJS acceptance, inference and diagnostics while doing this experiment.
Keep rejected safe programs as incompleteness findings; only behavior-preserving
claim extraction changes belong here. [DESIGN.md](DESIGN.md) owns this boundary.

For repair-coverage work, start with [REPAIR-COVERAGE.md](REPAIR-COVERAGE.md):
measurement, current checkpoint, inspected blockers and extension pitfalls.

## Commands

```sh
make verify                      # from the repo root: build, suites, then the corpus
make verify-census               # original SKJS repair functions (separate baseline)
make verify-test                 # the suites only
make verify-examples             # the corpus only
verification/run.sh --suite all  # the suites, without rebuilding Lean
lake -d verification/lean build  # the verifier alone
node verification/examples.mts    # the corpus alone, both producers
make verify-examples-skjs        # one column at a time; either alone runs
make verify-examples-tsc         # only that producer
make viewer                      # the claim report reader on http://localhost:8731
```

One file end to end, with `$F` a repository-relative path:

```sh
node verification/tools/fragment-parse.mts $F > ast.json
bash verification/skjs.sh --emit-skjs-type-claims $F > claims.json
verification/lean/.lake/build/bin/verifier --produce-stateful-source ast.json claims.json $F evidence.json 10
verification/lean/.lake/build/bin/verifier --check-skjs-operations claims.json
```

`skjs.sh` runs SKJS in the `skiplabs/skip` container; inside a devcontainer it
runs the binary directly. Never invoke `target/host/dev/skjs` yourself.

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
  corpus.

`examples.mts` follows the same rules on its own: one producer run for every
corpus file, one worker per core, and colour decided once in the parent.

## What a result means

- The corpus prints a pair per producer, `SKJS ✓→✓ · tsc ✓→✗`: the producer's
  own verdict on the program, then whether the verifier derives the claims it
  made. `✗` on the right means proof search found no derivation; it is never a
  disproof. `?` means the check could not be attempted. `⚠` marks an SKJS
  acceptance its own claims do not establish; the tsc column carries none,
  because exporter coverage and proof-search limits still need to be separated
  from unsoundness findings. TS now states primitive field-content assertions
  for direct reads at statement entry.
- Expected outcomes are policy, in `expectedVerified` in `examples.mts`: a
  witness fixture is expected *not* to verify, and a run fails when any
  function's outcome contradicts the policy, in either direction.
- Fixtures under `tests/skjs-unsound/` and `tests/skjs-incomplete/` are
  findings about SKJS and carry their own comment; the group README says what
  each tool does with them. Do not "fix" one so that it verifies.
- A repair is a hand-written candidate edit kept beside the original export,
  never an automatic widening of SKJS's claims.

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
  disambiguate. Staleness against a source is what the `sha256` fields are for,
  and they say it precisely rather than by a number.
- A format is never frozen and never has two accepted shapes. Fix its shape in
  place, then regenerate the fixtures that carry it. Do not add a compatibility
  shim, a second decoder, or a field that records which shape a document is:
  every producer and consumer of these documents is in this repository, nothing
  outside reads them, and there is no older document to keep working.
- Lean: no `sorry`, no project axioms; `#print axioms` on every soundness
  theorem stays in the file. Build only the module you changed while
  iterating (`lake build Verification.ExperimentState.<Module>`).
- Docs: a doc-only change needs no suite run; check anchors and prose.
