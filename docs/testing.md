# Testing Guide

## Test Organization

| Location | Purpose | Harness test |
| --- | --- | --- |
| `tests/expect-error/*.ts` | Positive + negative unit tests with diagnostic annotations | `testExpectError` |
| `tests/projects/*/` | Auto-discovered multi-file projects (with `tsconfig.json`) | `testProjects` |
| `examples/src/*.ts` | Working examples demonstrating supported patterns | `testExamples` |
| `tests/ts-conformance/` | Verbatim TypeScript conformance suite (see below) | `testTypeScriptConformance` / `testNotSupportedTypeScriptConformance` |
| `tests/{cfg,deadcode,constprop,callgraph,callgraph-unsupported}/` | Expectation tests for CFG, dead code, constant prop, call graph | `testCFG`, `testDeadCode`, `testConstantProp`, `testCallGraph*` |
| `tests/*.sk` | Unit tests for lexer, parser, module resolver, type ops, etc. | `skargo test` |
| `tests/test_*.sh` | End-to-end shell tests (incremental, incremental perf budget, affected files, stdin, config) | `make test` |

`testNoLostTest` enforces that no `.ts` or `.js` file sits uncovered under `tests/` or `examples/`.

## Running & Updating Tests

```bash
make test-in-docker                     # Full suite (every commit must pass)
make test-perf-in-docker                # Incremental latency budget against release binary
make test-cfg-in-docker                 # CFG expectation tests only
make test-deadcode-in-docker            # Dead-code expectation tests only
make check-file-in-docker FILE=tmp.ts BIN=./target/host/dev/skjs  # Single-file check
make fmt                                # Format (.sk via skfmt, .ts/.json via prettier)
```

Use native `make test` / `skargo test <filter>` when a local Skip toolchain is available; for comment-only changes, `make check-in-docker` / `skargo check` suffices.

### Updating diagnostic expectations

```bash
UPDATE_EXPECT=1 make test-in-docker   # Add missing annotations (also regenerates CFG/dead-code/constprop)
UPDATE_EXPECT=2 make test-in-docker   # Also rewrite existing annotation text
UPDATE_EXPECT=3 make test-in-docker   # Full rewrite + reorder alphabetically
```

- Preserves `@ts-expect-error` vs `@skjs-expect-error` prefixes; new diagnostics get `@skjs-expect-error` / `@skjs-expect-warning` (errors before warnings on a line).
- `@skjs-expect-error-lineN` pins the Nth continuation line of the error anchored by `@skjs-expect-error` above it (requires exactly one `@skjs-expect-error` in the group). The updater refreshes text for already-pinned `-lineN` lines and drops vanished ones, but never adds new `-lineN` pins.
- Always run `make test-in-docker` (without `UPDATE_EXPECT`) afterward to verify.

## Annotation & Authoring Rules

- **Typechecker, not a runtime**: Never invoke functions or call `console.log()` — code never executes. Wrap test code in functions (`function test(): void { ... }`) because SKJS disallows top-level `let` and non-void top-level statements.
- **Diagnostic annotations** (placed immediately before the offending line; also supported as `//` comments in `.json` files like `tests/projects/*/tsconfig.json`):
  - `// @ts-expect-error <exact message>` — error TypeScript (`tsc --strict --noEmit`) also produces
  - `// @skjs-expect-error <exact message>` — SKJS-specific error
  - `// @skjs-expect-error-lineN <exact line>` — optional continuation-line assertion (only with a single `@skjs-expect-error`)
  - `// @skjs-expect-warning <exact message>` — non-fatal lint warning (checked on a separate severity; a line with both an error and a warning needs both)
- **Multiple diagnostics on one line**: Use separate comment lines (one per diagnostic), never slash-separated messages. Avoid duplicate annotations on consecutive lines.
- **One error per definition**: Only the first fatal error per definition is reported (unless `--keep-going`). Use plain `// TODO:` (never `@ts-expect-error`) for shadowed errors. Warnings are non-fatal and all are reported.
- **Parse-error files**:
  - Must be named `*-prettier-ignore.ts` (skips prettier).
  - The parse error must be on the last non-empty line, including closing braces/brackets on that line (e.g. `error_here; }` not `error_here;\n}`).
  - Parse errors abort type-checking for the rest of the file — fix parse errors before debugging missing type errors.
- **Minimal & effective tests**:
  - Prefer extending an existing relevant test file over creating a new one.
  - Include both positive (accepted) and negative (producing an actual error) cases, one case per distinct context (classes, interfaces, type aliases, object literals, functions — test across contexts when relevant).
  - Run tests first to see actual messages before annotating.
  - Write comments describing current behavior, not historical changes.
  - Never delete failing tests to fix failures; document unimplemented negative checks or TS discrepancies with `// FIXME: ...`.

## Verifying Against TypeScript

- Verify expected behavior with `npx tsc --strict --noEmit <file>` (use `/tmp` for scratch checks).
- SKJS must not be more permissive than `tsc --strict` unless documented, and must not copy `tsc`'s soundness holes (see [typescript-soundness-holes.md](typescript-soundness-holes.md)).
- **"Currently rejected" ≠ "handled"**: Over-strict rejection often masks an unimplemented analog of a handled case. Check `tsc --strict` and check structural analogs explicitly across all key kinds (`string` / `number` / `symbol`).

## TypeScript Conformance Tests

`tests/ts-conformance/` holds files copied **verbatim** from [microsoft/TypeScript](https://github.com/microsoft/TypeScript) (`tsc/testdata/tests/cases/conformance/`, baselines in `tsc/testdata/baselines/reference/conformance/`). Never modify them.

- `cases/` — pass verbatim in **conformance mode** (`conformance: true`, see [skjs-rules.md](../skjs-rules.md#conformance-mode)), matched by error line numbers against `reference/<name>.errors.txt`. Allow-listed `// @param: value` headers (`allowedConfig` in `tests/Main.sk`) are stripped by `tsc`, so the harness adds the header count back to reference lines.
- `not-supported/` — verbatim files that must produce at least one error. Only move a file here (`mv`, verbatim) after genuinely trying to implement the missing support, and state the blocker in the PR description. Never copy straight into `not-supported/`.
- `reference/` — `.errors.txt` baselines, flat by basename.

Import workflow (from repo root):

```bash
devtools/copy-ts-tests.sh path/to/.../cases/conformance/some/dir   # copies into cases/
make test-in-docker
```
