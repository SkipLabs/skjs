# Commits and Pull Requests

## Commit Requirements

- Each commit must pass formatting (`make fmt`) and tests (`make test-in-docker`)
- Make one commit per logical change
- Bump the semantic version in `Skargo.toml` in every PR (patch for bug fixes, minor for new features or behavior changes, major for breaking changes). Do this as part of the PR, not a separate release commit.

## When to Update Documentation

- Update `skjs-rules.md` when adding or removing restrictions/features that differ from TypeScript
- Don't document standard TypeScript features that work identically in SKJS
- Include examples for new restrictions
- Update in the same commit or PR as the feature/restriction change

## Pull Request Guidelines

- Keep PR descriptions concise — focus on the summary and motivation
- Don't list every file change in the PR description — reviewers will see the files in the diff
- Example: "Add tests for error messages and fix comment style" is sufficient; no need to enumerate each test file
