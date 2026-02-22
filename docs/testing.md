# Testing Guide

## Test Organization

- **Runnable examples**: `examples/src/*.ts` — demonstrate working features and patterns
- **Unit tests**: `tests/expect-error/*.ts` — both positive (valid code) and negative (invalid code with error annotations) tests
- **Test projects**: `tests/projects/*/` — multi-file projects, auto-discovered (all must pass at every commit)

## Running Tests

```bash
make build-in-docker    # Build
make test-in-docker     # Run all tests (every commit must pass)
make check-in-docker    # Type-check Skip code without building
make fmt                # Format code (skfmt for .sk, prettier for .ts/.json)
```

## Critical Rules

**SKJS is a typechecker, not a runtime**:
- Don't call functions or use `console.log()` — the code never executes
- Tests exercise type-checking behavior only
- Example: `const x: number = "hello";` tests type errors, not runtime values

**Error annotations**:
- Use `// @ts-expect-error <exact error message>` for errors TypeScript would also produce
- Use `// @skjs-expect-error <exact error message>` for SKJS-specific errors
- Run tests first to see actual error messages, then add the annotations with exact wording
- **SKJS reports only one type error per definition** — if a function has multiple issues, only the first error is reported (unless passing `--keep-going`, which is best-effort — fatal errors may still hide subsequent ones)
- For expected errors that aren't reported due to an earlier error, use plain `// TODO:` comments (not `@ts-expect-error`)
- **Multiple errors on a single line**: use multiple `@skjs-expect-error` comment lines, one per error. Do NOT use slash-separated errors in a single comment.
- **Avoid duplicate annotations**: use `@ts-expect-error` for TypeScript-specific errors and `@skjs-expect-error` for SKJS errors. Don't duplicate the same annotation twice on consecutive lines.

**Parse error constraints**:
- Parse errors must appear on the last non-empty line of the file
- Files with intentional parse errors must be named `*-prettier-ignore.ts` to skip prettier formatting
- The error line should end with closing braces/brackets if needed (e.g., `error_here; }` not `error_here;\n}`)

**No top-level statements**:
- SKJS disallows top-level `let` and standalone statements
- Wrap test code in functions: `function test(): void { /* test code here */ }`

**Keep tests minimal**:
- One test case per context is sufficient — no need for many variations of the same test
- Don't test the same thing multiple times with different values
- Avoid redundant test cases (e.g., `field1`, `field2`, `field3` that all do exactly the same thing)

**Matching TypeScript behavior**:
- SKJS should not be more permissive than TypeScript
- When discovering SKJS accepts something TypeScript rejects, fix SKJS to match TypeScript's stricter behavior
- Use TypeScript (`npx tsc --noEmit <file>`) to verify expected behavior when in doubt
- When SKJS differs from TypeScript, document the discrepancy with a `// FIXME:` comment explaining what TypeScript does
- Create regression tests for known discrepancies using `@skjs-expect-error` and FIXME comments

**SKJS-specific type system differences**:
- Array literals use delayed typing — `[...]` commits to array or tuple based on usage context (type annotation, method calls, etc.)
- Once committed, the type cannot change (e.g., using `.push()` commits to array, then assigning to a tuple type is an error)
- SKJS requires explicit type annotations on class and object type fields (stricter than TypeScript's implicit `any`)

**Writing effective tests**:
- Always include both positive (valid code) and negative (invalid code with errors) test cases
- Negative tests must produce actual type errors — if the "wrong" behavior still type-checks, the test is ineffective
- Focus on type checking, never on runtime values or expected outputs
- Avoid SKJS-unsupported features in tests (e.g., `as` casts, `any` type)
- Use `??` to handle potentially undefined values (e.g., `arr[i] ?? 0` for array access)
- If testing requires specific types, use function parameters instead of complex type annotations

## Updating Error Annotations

When error messages change, update all `@ts-expect-error` and `@skjs-expect-error` annotations automatically:

```sh
UPDATE_EXPECT=1 make test-in-docker   # Add missing annotations, preserve existing
UPDATE_EXPECT=2 make test-in-docker   # Also rewrite existing annotation text
UPDATE_EXPECT=3 make test-in-docker   # Full rewrite + reorder alphabetically
```

This rewrites annotations in `tests/expect-error/` and `examples/src/` to match actual error messages, preserving the `@ts-expect-error` vs `@skjs-expect-error` prefix. New errors get `@skjs-expect-error` by default. Run `make test-in-docker` afterward to verify.

## Regression and Edge Cases

**Testing syntax restrictions**:
- Test edge cases across all relevant contexts: classes, interfaces, type aliases, object literals, functions, ...
- Consider whether modifier or other keywords can be used as field/method/variable names in each context
- Example: if restricting syntax in classes, verify the same keyword works in object types
- Add FIXME tests documenting where SKJS behavior differs from TypeScript

**Verifying with TypeScript**:
- Always check TypeScript's behavior with `npx tsc --strict --noEmit <file>` when creating regression tests
- Use `--strict` mode to catch errors TypeScript would normally miss (e.g., null checks)
- Create temporary test files in `/tmp` for quick verification without polluting the test suite
- Don't assume SKJS and TypeScript have the same restrictions — verify each case

**Parse errors hide type errors**:
- SKJS stops checking after encountering a parse error — subsequent type errors won't be reported
- If many error annotations aren't triggering, check for parse errors first in the test output
- Fix parse errors before debugging missing type errors
- Common culprits: unsupported syntax, typos in keywords, wrong operators

**Negative tests that don't error**:
- Not all incorrect code produces errors in SKJS — some checks aren't implemented yet
- When a negative test doesn't error, document it with FIXME rather than removing it
- Example: `// FIXME: TypeScript catches this error but SKJS doesn't`
- These tests document gaps and guide future improvements

## Common Mistakes

1. **Don't use console.log or function calls in tests** — we're testing a typechecker, not a runtime
2. **Don't batch expect-error comments** — place them immediately before the error line
3. **Don't create new files unnecessarily** — prefer modifying existing test files over creating new ones unless testing a distinct feature
4. **Don't add expect-error comments before running tests** — see the actual error message first, then annotate
5. **Don't put code after parse errors** — parse errors must be on the last non-empty line
6. **Don't write comments about changes** — comments should describe the current state (e.g., "Test multiple errors per class") not changes (e.g., "Test that multiple errors per class are now reported")
7. **Don't remove tests to fix test failures** — fix the annotations or test logic properly instead of deleting the failing test case
8. **Don't use `@ts-expect-error` in TODO comments** — use plain `// TODO:` for errors that won't be reported due to an earlier error in the function
9. **Don't assume SKJS matches TypeScript** — when creating regression tests, verify TypeScript's actual behavior first
10. **Don't forget to test across contexts** — a syntax restriction in one context (classes) may need tests in others (interfaces, types, object literals)
