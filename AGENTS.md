# SKJS

TypeScript type checker implemented in the Skip language (`.sk`). Aims to check a sound subset of TypeScript — rejecting programs that would fail at runtime for type reasons. Soundness is the goal rather than a finished guarantee: some unsound programs are still accepted today.

- `src/*.sk` + `src/absint/*.sk` — checker implementation (Skip)
- `tests/*.sk` — test harness (Skip)
- `tests/expect-error/*.ts`, `tests/projects/*/`, `examples/src/*.ts` — TypeScript user programs checked by SKJS

## Commands

```bash
make check-in-docker                                # Fast incremental type-check of Skip code
make build-in-docker                                # Build ./target/host/dev/skjs
make check-file-in-docker FILE=tmp.ts               # Check one TS file via `skargo run`
make check-file-in-docker FILE=tmp.ts BIN=./target/host/dev/skjs  # Reuse built binary (faster)
make test-in-docker                                 # Full suite — every commit must pass
make test-cfg-in-docker / make test-deadcode-in-docker  # Targeted CFG / dead-code tests
make fmt                                            # Format (.sk via skfmt, .ts/.json via prettier)
make check-fmt && make check-sh                     # CI formatting + shellcheck/selftests
make clean-in-docker                                # Clean build artifacts
```

`*-in-docker` runs inside the Skip docker image (directly in a devcontainer). With a local Skip toolchain, use `make build` / `make test` / `make check` or `skargo` directly. For comment-only changes, `make check-in-docker` / `skargo check` suffices.

To check a project with `node_modules` dependencies, layer `--import-stubs` (the first directory provides `@types/skjs` builtins; `import-stubs/` stays the default fallback for SKJS's own tests):

```bash
./target/host/dev/skjs check --import-stubs ./import-stubs --import-stubs ./node_modules src/index.ts
```

### Fast debugging loop

- Save binary variants to compare before/after on a `tmp_*.ts` repro (gitignored):
  `cp target/host/dev/skjs target/host/dev/skjs.<label>`, then pass `BIN=target/host/dev/skjs.<label>`.
- Inspect inferred types in `.ts` repros with intrinsics:
  - `__SKJS_show(expr)` — inferred type (often alias-preserving)
  - `__SKJS_show_expanded(expr)` — expanded type (useful for tuple-rest/internal debugging)
  - Optional 2nd string-literal arg asserts the printed type, e.g. `__SKJS_show_expanded(x, "[]")`.
- Update test expectations after diagnostic changes: `UPDATE_EXPECT=1|2|3 make test-in-docker` (see [docs/testing.md](docs/testing.md)).

## Codebase Map

| Area | Key files |
| --- | --- |
| CLI & driver | `src/Main.sk`, `src/Files.sk`, `src/Config.sk`, `src/TsConfig.sk`, `src/ModuleResolver.sk`, `src/FileDefs.sk` |
| Lexer & parser | `src/Lexer.sk`, `src/Tokens.sk`, `src/Ast.sk`, `src/Parser.sk`, `src/Parser{Defs,Expr,Stmt,Type,Pattern,Utils}.sk` |
| Type representation | `src/TType.sk`, `src/TType{Union,Inter,Subst,Subtyping,Observation,Materialization,Transformers,Pp}.sk`, `src/TEnv.sk` |
| Type checker | `src/TypeCheck.sk`, `src/TypeCheck{Def,Class,Enum,Fun,Stmt,Expr,Refine,Scope,Env,Utils}.sk`, `src/TArrayLitTyping.sk`, `src/TVariadicTyping.sk`, `src/CallTyping.sk`, `src/CaptureWrites.sk` |
| Diagnostics | `src/Error.sk`, `src/TypingError.sk`, `src/Position.sk` |
| Abstract interp / CFG | `src/absint/{CFG,CFGSerializer,AbstractDomain,ConstantProp,DeadCode,InterprocDataflow}.sk` |
| Tests & stubs | `tests/Main.sk`, `tests/Helpers.sk`, `tests/expect-error/*.ts`, `tests/projects/*/` (auto-discovered), `tests/ts-conformance/`, `examples/src/*.ts`, `import-stubs/` |

## Key Conventions

- **Green commits**: Every commit must pass `make fmt` and `make test-in-docker`.
- **Pinning tests first**: Add a pinning test demonstrating the current behavior in its own commit BEFORE the fix/behavior-change commit — never in the same commit (sole exception: pre-change test crashes the runner). See [docs/commits-and-prs.md](docs/commits-and-prs.md).
- **One logical change per commit**; bump `version` in `Skargo.toml` in every code PR (patch/minor/major).
- **No build/debug artifacts**: Never commit `target/`, `tmp_*.ts`, `_skjs-debug/`, or caches (all gitignored).
- **SKJS is a typechecker, not a runtime**: Tests exercise type-checking only — no `console.log()` or function invocations.
- **One error per definition**: SKJS reports only the first fatal error per definition unless `--keep-going` is passed (best-effort). Warnings are non-fatal and all are reported.
- **Match TypeScript, never its unsoundness**: SKJS must not be more permissive than `tsc --strict --noEmit`, except where documented, and must not follow `tsc` when `tsc` is unsound.
- **Skip-code lessons log**: Read [SkipLabs/skip `docs/skip-code-notes.md`](https://github.com/SkipLabs/skip/blob/main/docs/skip-code-notes.md) (sibling checkout: `../skip/docs/skip-code-notes.md`) before writing `.sk` code; append Skip-writing lessons there in the Skip repo.

## Merge bot

`bin/merge-bot.sh` delegates to `../skip/bin/merge-bot.sh` (override with `SKIP_DIR`), setting skjs CI heuristics, `.vibe/skills/merge-bot/references/`, and state dir `~/.cache/skjs-merge-bot`. Use the `merge-bot` skill (symlinked to `../skip/.vibe/skills/merge-bot/SKILL.md`) or `bin/merge-bot.sh run` (`--dry-run` to preview); `bin/merge-bot.sh --selftest` runs via `make check-sh`.

## Detailed Guides

Read the relevant guide before starting a task:

| Guide | When to read |
| --- | --- |
| [Setup](docs/setup.md) | First-time setup (sibling `../skip`, git hooks) |
| [TypeScript Subset Rules](skjs-rules.md) | Normative spec of what SKJS accepts/rejects (has ToC — jump to the relevant rule) |
| [TypeScript Soundness Holes](docs/typescript-soundness-holes.md) | Before deciding whether to follow `tsc` — catalogues unsound programs `tsc --strict` accepts |
| [Writing Code](docs/writing-code.md) | Skip style, error message conventions, doc-sync rules |
| [Skip Code Notes](https://github.com/SkipLabs/skip/blob/main/docs/skip-code-notes.md) | Canonical Skip-writing lessons (in sibling `../skip/docs/skip-code-notes.md`) |
| [Testing](docs/testing.md) | Annotations, `UPDATE_EXPECT`, conformance tests, test rules |
| [Commits and PRs](docs/commits-and-prs.md) | Commit ordering, versioning, AI disclosure, PR guidelines |
| [Error Formats](docs/error-format.md) | `--error-format` (`default`, `indent`, `json`) schemas |
| [Incremental](docs/incremental.md) | `--init` / `--data` / `--log-affected-files` |
| [Releasing & CI](docs/releasing.md) | CircleCI change classification, binary cache, release tagging |
