# SKJS

TypeScript type checker implemented in the Skip language. It checks a sound subset of TypeScript — programs that pass SKJS will not fail at runtime for type reasons.

- **`.sk` files** in `src/` are the checker implementation (Skip language)
- **`.ts` files** in `tests/` and `examples/` are TypeScript user programs checked by SKJS

## Commands

```bash
make build-in-docker    # Build (produces ./target/host/dev/skjs)
make test-in-docker     # Run all tests — every commit must pass this
make check-in-docker    # Type-check the Skip code without building
make fmt                # Format all code (skfmt for .sk, prettier for .ts/.json)
make clean-in-docker    # Clean build artifacts
```

## Project Layout

| Path | Contents |
| --- | --- |
| `src/*.sk` | Type checker implementation (~49 files): lexer, parser, type checker, module resolver |
| `tests/expect-error/*.ts` | Negative + positive type-checking tests with error annotations |
| `examples/src/*.ts` | Working example programs demonstrating supported features |
| `tests/projects/*/` | Multi-file test projects (auto-discovered — all must pass at every commit) |
| `import-stubs/` | Stub type declarations for built-in modules |

## Key Conventions

- **Commit prefix**: All AI-generated commits and PR titles must start with `AIGEN`
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
