# Contributors Guide

## Overview

- SKJS is written in the Skip language.
- When changing the TypeScript support surface, update [skjs-rules.md](skjs-rules.md) in the same commit or PR so the documented subset matches reality (include new restrictions, lifted gaps, and workarounds).
- Add or adjust tests whenever diagnostics, typing rules, or code generation changes—`skargo test` must stay green.
- **Update this document** - When you learn something useful while contributing, add it here! This guide grows from real experience. Common pitfalls, debugging tricks, and workflow tips belong here.

## Writing Tests

### Test Organization
- **Runnable examples**: `examples/src/*.ts` - Demonstrate working features and patterns
- **Unit tests**: `tests/expect-error/*.ts` - Both positive (valid code) and negative (invalid code with error annotations) tests

### Critical Test Writing Rules

**SKJS is a typechecker, not a runtime**:
- Don't call functions or use `console.log()` - the code never executes
- Tests exercise type-checking behavior only
- Example: `const x: number = "hello";` tests type errors, not runtime values

**Error annotations**:
- Use `// @ts-expect-error <exact error message>` for errors TypeScript would also produce
- Use `// @skjs-expect-error <exact error message>` for SKJS-specific errors
- Run tests first to see actual error messages, then add the annotations with exact wording
- **SKJS reports only one type error per definition** - If a function has multiple issues, only the first error is reported
- For expected errors that aren't reported due to an earlier error, use plain `// TODO:` comments (not `@ts-expect-error`)
- **Multiple errors on a single line**: When SKJS reports multiple errors for a single line (e.g., both "Construction not supported" and "Invalid return type"), use multiple `@skjs-expect-error` comment lines, one per error. Do NOT use slash-separated errors in a single comment.
- **Avoid duplicate annotations**: Use `@ts-expect-error` for TypeScript-specific errors and `@skjs-expect-error` for SKJS errors. Don't duplicate the same annotation twice on consecutive lines.

**Parse error constraints**:
- Parse errors must appear on the last non-empty line of the file
- Files with intentional parse errors must be named `*-prettier-ignore.ts` to skip prettier formatting
- The error line should end with closing braces/brackets if needed (e.g., `error_here; }` not `error_here;\n}`)

**No top-level statements**:
- SKJS disallows top-level `let` and standalone statements
- Wrap test code in functions: `function test(): void { /* test code here */ }`

**Keep tests minimal**:
- One test case per context is sufficient - no need for many variations of the same test
- Don't test the same thing multiple times with different values
- Avoid redundant test cases (e.g., `field1`, `field2`, `field3` that all do exactly the same thing)

**Matching TypeScript behavior**:
- SKJS should not be more permissive than TypeScript
- When discovering SKJS accepts something TypeScript rejects, fix SKJS to match TypeScript's stricter behavior
- Use TypeScript (`npx tsc --noEmit <file>`) to verify expected behavior when in doubt
- When SKJS differs from TypeScript, document the discrepancy with a `// FIXME:` comment explaining what TypeScript does
- Create regression tests for known discrepancies between SKJS and TypeScript using `@skjs-expect-error` and FIXME comments

**SKJS-specific type system differences**:
- In SKJS, tuples are not compatible with arrays - the `[...]` syntax is for tuples only, both in types and values
- Tuple types like `[number, string]` are distinct from array types
- SKJS requires explicit type annotations on class and object type fields (stricter than TypeScript's implicit `any`)

**Writing effective tests**:

- Always include both positive (valid code) and negative (invalid code with errors) test cases
- Negative tests must produce actual type errors - if the "wrong" behavior still type-checks, the test is ineffective
- Focus on type checking, never on runtime values or expected outputs
- Avoid SKJS-unsupported features in tests (e.g., `as` casts, `any` type)
- Use `??` to handle potentially undefined values (e.g., `arr[i] ?? 0` for array access)
- If testing requires specific types, use function parameters instead of complex type annotations

### Running Tests

**Prerequisites:** The [Skip repository](https://github.com/SkipLabs/skip) must be checked out as a sibling directory (`../skip`).

```bash
# Run all tests
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo test

# Check a specific file
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo check <file>
```

## Commit Guidelines

### Commit Requirements
- Each commit must pass formatting (`make fmt`)
- Run `make setup-git-hooks` once to set up automatic formatting checks
- Each commit must pass tests (`skargo test`)
- Make one commit per logical change
- Message must start with `AIGEN` if code was produced with AI assistance

### When to Update Documentation
- Update `skjs-rules.md` when adding or removing restrictions/features that differ from TypeScript
- Don't document standard TypeScript features that work identically in SKJS
- Include examples for new restrictions
- Update in the same commit or PR as the feature/restriction change

### Pull Request Guidelines

- Keep PR descriptions concise - focus on the summary and motivation
- Don't list every file change in the PR description - reviewers will see the files in the diff
- Example: "Add tests for error messages and fix comment style" is sufficient; no need to enumerate each test file

## Testing Regression and Edge Cases

When adding tests for parser or type system changes:

**Testing syntax restrictions**:
- Test edge cases across all relevant contexts: classes, interfaces, type aliases, object literals, functions, ...
- Consider whether modifier or other keywords can be used as field/method/variable names in each context
- Example: If restricting syntax in classes, verify the same keyword works in object types
- Add FIXME tests documenting where SKJS behavior differs from TypeScript

**Verifying with TypeScript**:
- Always check TypeScript's behavior with `npx tsc --strict --noEmit <file>` when creating regression tests
- Use `--strict` mode to catch errors TypeScript would normally miss (e.g., null checks)
- Create temporary test files in `/tmp` for quick verification without polluting the test suite
- Don't assume SKJS and TypeScript have the same restrictions - verify each case

**Parse errors hide type errors**:
- SKJS stops checking after encountering a parse error - subsequent type errors won't be reported
- If many error annotations aren't triggering, check for parse errors first in the test output
- Fix parse errors before debugging missing type errors
- Common culprits: unsupported syntax, typos in keywords, wrong operators

**Negative tests that don't error**:
- Not all incorrect code produces errors in SKJS - some checks aren't implemented yet
- When a negative test doesn't error, document it with FIXME rather than removing it
- Example: `// FIXME: TypeScript catches this error but SKJS doesn't`
- These tests document gaps and guide future improvements

## Common Mistakes to Avoid

1. **Don't use console.log or function calls in tests** - We're testing a typechecker, not a runtime
2. **Don't batch expect-error comments** - Place them immediately before the error line
3. **Don't forget AIGEN prefix** - All AI-generated commits need it
4. **Don't create new files unnecessarily** - Prefer modifying existing test files over creating new ones unless testing a distinct feature
5. **Don't add expect-error comments before running tests** - See the actual error message first, then annotate
6. **Don't put code after parse errors** - Parse errors must be on the last non-empty line
7. **Don't write comments about changes** - Comments should describe the current state (e.g., "Test multiple errors per class") not changes (e.g., "Test that multiple errors per class are now reported")
8. **Don't remove tests to fix test failures** - Fix the annotations or test logic properly instead of deleting the failing test case
9. **Don't use `@ts-expect-error` in TODO comments** - Use plain `// TODO:` for errors that won't be reported due to an earlier error in the function
10. **Don't assume SKJS matches TypeScript** - When creating regression tests, verify TypeScript's actual behavior first
11. **Don't forget to test across contexts** - A syntax restriction in one context (classes) may need tests in others (interfaces, types, object literals)
