# SKJS

TypeScript type checker implemented in the Skip language. It checks a sound subset of TypeScript — programs that pass SKJS will not fail at runtime for type reasons.

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

- **Green commits**: Every intermediate commit must pass `make test-in-docker`
- **SKJS is a typechecker, not a runtime**: Tests exercise type-checking only — no `console.log()` calls or function invocations
- **One error per definition**: SKJS reports only the first type error per function/definition unless passing `--keep-going` (best-effort — fatal errors may still hide subsequent ones)
- **Match TypeScript**: SKJS should not be more permissive than TypeScript, but must not follow TypeScript when TypeScript is unsound. When in doubt, verify with `npx tsc --strict --noEmit`

## Detailed Guides

Read these before starting the relevant task:

| Guide | When to read |
| --- | --- |
| [Setup](docs/setup.md) | First time setting up the repo |
| [TypeScript Subset Rules](skjs-rules.md) | Before changing what SKJS accepts or rejects — this is the source of truth |
| [Writing Code](docs/writing-code.md) | Before writing or modifying `.sk` or `.ts` files |
| [Testing](docs/testing.md) | Before writing or modifying tests |
| [Commits and PRs](docs/commits-and-prs.md) | Before committing or opening a pull request |
