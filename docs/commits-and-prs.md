# Commits and Pull Requests

## Commit Requirements

- Each commit must pass formatting (`make fmt`) and tests (`make test-in-docker`)
- Make one commit per logical change
- Bump the semantic version in `Skargo.toml` in every PR (patch for bug fixes, minor for new features or behavior changes, major for breaking changes). Do this as part of the PR, not a separate release commit.

## Commit Ordering

- **Tests before code.** Introduce test cases in a commit _before_ the code change that affects them, annotated for the then-current behavior (`@skjs-expect-error` with the pre-change message, or no annotation if the case is silently accepted). The code commit then only flips the annotations, so its diff demonstrates the behavior change. This is always possible with expect-error tests: "the asserted error doesn't exist yet" just means the pre-change annotation is different or absent, not that the test can't be introduced first.
- **Fixes and infrastructure before the feature that depends on them.** When work spans a fix or refactor and a new feature, commit the fix/infrastructure first, so each commit is self-contained, green, and reviewable in order.

## When to Update Documentation

- Update `skjs-rules.md` when adding or removing restrictions/features that differ from TypeScript
- Don't document standard TypeScript features that work identically in SKJS
- Include examples for new restrictions
- Update in the same commit or PR as the feature/restriction change

## Pull Request Guidelines

- Keep PR descriptions concise — focus on the summary and motivation
- Don't list every file change in the PR description — reviewers will see the files in the diff
- Example: "Add tests for error messages and fix comment style" is sufficient; no need to enumerate each test file
