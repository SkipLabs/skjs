# Commits and Pull Requests

## Commit Requirements

- Each commit must pass formatting (`make fmt`) and tests (`make test-in-docker`)
- Make one commit per logical change — never two concerns in one commit, even when they feel related. Natural seams: fix vs. feature, refactor vs. behavior change, infrastructure vs. consumer. An "and", "also", or ";" in the commit subject is a red flag. Before committing, ask: could a reviewer want to approve one half and reject the other? If yes, split.
- Bump the semantic version in `Skargo.toml` in every PR (patch for bug fixes, minor for new features or behavior changes, major for breaking changes). Do this as part of the PR, not a separate release commit.

## Commit Ordering

- **Tests before code.** Introduce test cases in a commit _before_ the code change that affects them, annotated for the then-current behavior (`@skjs-expect-error` with the pre-change message, or no annotation if the case is silently accepted). The code commit then only flips the annotations, so its diff demonstrates the behavior change. This is always possible with expect-error tests: "the asserted error doesn't exist yet" just means the pre-change annotation is different or absent, not that the test can't be introduced first.
- **Fixes and infrastructure before the feature that depends on them.** When work spans a fix or refactor and a new feature, commit the fix/infrastructure first, so each commit is self-contained, green, and reviewable in order.

## AI Disclosure

Never mask the use of AI. When AI wrote or co-wrote a change:

- Credit it in the commit with a `Co-Authored-By` trailer naming the provider, model, version, and effort/reasoning setting, e.g.:

  ```text
  Co-Authored-By: Claude Fable 5 (Anthropic claude-fable-5[1m], effort high) <noreply@anthropic.com>
  ```

- Include the effort/reasoning setting only when it is actually known. When the tool does not expose it, omit it rather than padding with a guess — "default effort" conveys nothing.

- Report the model and settings that were in effect **when the code was written**, not when the commit was created — e.g. code written by one model but committed later (split, cherry-picked, rebased) under another still credits the model that wrote it. Use one trailer per AI that contributed.
- Disclose AI assistance in PR descriptions the same way.

## When to Update Documentation

- Update `skjs-rules.md` when adding or removing restrictions/features that differ from TypeScript
- Don't document standard TypeScript features that work identically in SKJS
- Include examples for new restrictions
- Update in the same commit or PR as the feature/restriction change

## Pull Request Guidelines

- Keep PR descriptions concise — focus on the summary and motivation
- Don't list every file change in the PR description — reviewers will see the files in the diff
- Example: "Add tests for error messages and fix comment style" is sufficient; no need to enumerate each test file
