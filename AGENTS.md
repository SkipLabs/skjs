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

## Merge bot

`bin/merge-bot.sh` (driven by the `.vibe/skills/merge-bot` skill) runs the merge queue. A PR is ready when **auto-merge is enabled and its CI is green** (the required `ci/circleci: build` check); PRs with red CI are never considered. Among ready PRs the bot acts on **one at a time**: green + up-to-date PRs are simply waited on until auto-merge lands them (no rebase is scheduled until they have merged); green + not-up-to-date PRs (`BEHIND`/conflicting, i.e. `main` moved ahead) are rebased onto `main` — fastest expected CI first (the PR's last pipeline wall time, else a changed-paths heuristic) — then pushed with `--force-with-lease`. Run from a clone of this repo and the bot reuses that clone, doing the git work in `git worktree`s under `~/.cache/skjs-merge-bot` (never in your checkout's working tree, no second clone); run from elsewhere and it keeps a dedicated clone under `~/.cache/skjs-merge-bot`. Fork-headed PRs are included when they allow maintainer edits ("Allow edits from maintainers"), which lets maintainers push to the fork's branch; the bot then pushes the rebase to the fork. If `main` moves again while the bot waits on a rebased PR (strict required checks block merging a `BEHIND` PR), the bot re-rebases, up to `MERGE_BOT_REBASE_ATTEMPTS` (default 3) rounds. Rebase conflicts (and CI failures the rebase triggers) are handed to a sub-agent (`.vibe/skills/merge-bot/references/fix-conflicts.md` / `fix-ci.md`); if a fix is non-trivial, the bot comments on the PR, disables auto-merge, and skips it for now. Otherwise it waits until GitHub's auto-merge actually lands the PR before moving to the next one.

Run it interactively through the `merge-bot` skill, or unattended with `bin/merge-bot.sh run` (see `bin/merge-bot.sh --help`; `--dry-run` previews without pushing). `bin/merge-bot.sh --selftest` unit-tests the readiness/CI-estimate logic and runs as part of `make check-sh`.

## Project Layout

| Path | Contents |
| --- | --- |
| `src/*.sk` | Type checker implementation (~61 files): lexer, parser, type checker, module resolver |
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
| [TypeScript Soundness Holes](docs/typescript-soundness-holes.md) | Before deciding whether to follow tsc — catalogues the programs tsc accepts unsoundly |
| [Writing Code](docs/writing-code.md) | Before writing or modifying `.sk` or `.ts` files |
| [Testing](docs/testing.md) | Before writing or modifying tests |
| [Commits and PRs](docs/commits-and-prs.md) | Before committing or opening a pull request |
