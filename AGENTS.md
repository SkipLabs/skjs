# SKJS

TypeScript type checker implemented in the Skip language. It aims to check a sound subset of TypeScript — rejecting programs that would fail at runtime for type reasons. Soundness is the goal rather than a finished guarantee: some unsound programs are still accepted today.

- **`.sk` files** in `src/` are the checker implementation (Skip language)
- **`.sk` files** in `tests/` are the test harness
- **`.ts` files** in `tests/` and `examples/` are TypeScript user programs checked by SKJS

## Commands

```bash
make build-in-docker                   # Build the skjs binary
make check-file-in-docker FILE=tmp.ts  # Run skjs check on one file (fast iteration)
make test-in-docker                    # Run all tests — every commit must pass this
make check-in-docker                   # Type-check the Skip code without building (fast incremental)
make fmt                               # Format all code (skfmt for .sk, prettier for .ts/.json)
make clean-in-docker                   # Clean build artifacts
```

The `*-in-docker` targets run inside the Skip docker image (directly when in a devcontainer). With a local Skip toolchain, the native equivalents work too: `make build`, `make test`, `make check`, or `skargo` directly. For comment-only changes, `make check-in-docker` / `skargo check` is sufficient verification — comments cannot affect behavior, and it is much faster than the full test run.

## Fast Iteration (Single File + Binary Variants)

Use this loop for checker debugging (much faster than full builds/tests):

```bash
make build-in-docker
make check-file-in-docker FILE=tmp_atarrayof_semantic_fail.ts
make check-file-in-docker FILE=tmp_atarrayof_semantic_fail.ts BIN=target/host/dev/skjs.some-variant
```

Notes:

- `check-file-in-docker` defaults to `BIN=./target/host/dev/skjs`; override `BIN=...` to compare variants on the same repro.
- Save binary variants manually when iterating on one code change:

```bash
cp target/host/dev/skjs target/host/dev/skjs.<label>
```

- Debug type inference/normalization with show intrinsics inside `.ts` repros:
  - `__SKJS_show(expr)` prints the inferred type (often alias-preserving).
  - `__SKJS_show_expanded(expr)` prints an expanded type (useful for internals/tuple-rest debugging).
  - Optional 2nd arg string literal asserts the expected printed type (e.g. `__SKJS_show_expanded(x, "[]")`).

## Project Layout

| Path | Contents |
| --- | --- |
| `src/*.sk` | Type checker implementation (~49 files): lexer, parser, type checker, module resolver |
| `tests/*.sk` | Test harness (Skip test files) |
| `tests/expect-error/*.ts` | Negative + positive type-checking tests with error annotations |
| `examples/src/*.ts` | Working example programs demonstrating supported features |
| `tests/projects/*/` | Multi-file test projects (auto-discovered — all must pass at every commit) |
| `import-stubs/` | Stub type declarations for built-in modules |

## Key Conventions

- **Push permission**: Always ask the user for explicit permission before each push. Commit, integration, or PR preparation requests do not authorize pushing. A readiness question such as "Ready to push?" is not permission; report readiness and ask before running the push. Do not reuse approval from an earlier push.
- **Green commits**: Every intermediate commit must pass `make test-in-docker`
- **SKJS is a typechecker, not a runtime**: Tests exercise type-checking only — no `console.log()` calls or function invocations
- **One error per definition**: SKJS reports only the first type error per function/definition unless passing `--keep-going` (best-effort — fatal errors may still hide subsequent ones)
- **Match TypeScript**: SKJS should not be more permissive than TypeScript, but must not follow TypeScript when TypeScript is unsound. When in doubt, verify with `npx tsc --strict --noEmit`

## Resolving checker/verifier disagreements

- The semantic model is the reference: an allocated location has one fixed
  world type. Its current contents may narrow or change within that type;
  assignment must not change the location's type. Inference may determine a
  symbolic contract, but must preserve all earlier obligations when resolving it.
- Trace acceptance to the actual checker condition and retained inference state,
  then trace the exported fields through their consumers. An internal field
  named `declaredType` or a producer success flag is not itself a justification.
- Distinguish point-specific contents, enforced write contracts and candidate
  invariants. Do not synthesize a union, weaken an obligation, or reinterpret a
  point type as a lifetime contract just to make a repair example verify. A
  separately found proof of the program does not validate SKJS's own reasoning.
- When SKJS accepts a write without maintaining the required contract, treat it
  as a checker defect to investigate, not an exporter feature to accommodate.
  Correct export omissions when the checker already has the justification;
  repair the checker when that justification is missing. Existing acceptance
  tests record behavior and do not override the specified invariant.
- Respect task scope: pipeline-only work preserves SKJS behavior unless the user
  authorizes checker repairs. Once authorized, a demonstrated contract violation
  does not require another policy choice from the user. Keep the checker repair
  separate from unrelated fragment extensions.
- Report the original target's actual outcome. If a new feature works but its
  motivating repair still does not verify, say so explicitly, name the remaining
  obstruction, and continue within scope or identify what prevents progress.
  Passing suites and a recorded limitation do not make that target complete.

## Architectural refactoring status

The completed repair/lifetime audit is not completion of the stronger
architectural refactoring. Follow A1–A4 in
[the architectural end-state plan](docs/skjs-improvement.md#architectural-end-state).
Measure progress by restricted capabilities, separated proposal/validation/publication,
and retired unrestricted paths. More guards or passing regressions alone do not
establish separation. Keep remaining runtime enforcement and incomplete migrations
explicit; do not describe the reorganization as complete while those milestones
remain open.

## Measuring checker repair tests

When adding or regrouping repair regressions, run `make verify-census` in the
checkout containing their commits. It selects the repair arc's committed
TypeScript functions; `make verify-examples` only measures the curated viewer
examples, and native Skip tests are outside the source corpus. Review changed
producer outcomes and refusal reasons before recording `UPDATE=1`. Keep an
independent regression family in its own file when unrelated top-level aliases
would otherwise prevent meaningful extraction; do not simplify a witness to
make it verify. Report rejected, gated and verified outcomes separately.

## Detailed Guides

Read these before starting the relevant task:

| Guide | When to read |
| --- | --- |
| [Setup](docs/setup.md) | First time setting up the repo |
| [TypeScript Subset Rules](skjs-rules.md) | Before changing what SKJS accepts or rejects — this is the source of truth |
| [TypeScript Soundness Holes](docs/typescript-soundness-holes.md) | Before deciding whether to follow tsc — catalogues the programs tsc accepts unsoundly |
| [Writing Code](docs/writing-code.md) | Before writing or modifying `.sk` or `.ts` files |
| [Testing](docs/testing.md) | Before writing or modifying tests |
| [Commits and PRs](docs/commits-and-prs.md) | Before committing or opening a pull request |
| [Verification](verification/AGENTS.md) | Before touching `verification/`: the independent verifier, its suite's shape and rules, and what its results mean |
| [SKJS improvement](docs/skjs-improvement.md) | Before changing the checker to be more principled: contracts, active rows, and what not to do |
