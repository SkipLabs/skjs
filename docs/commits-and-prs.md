# Commits and Pull Requests

## Commit Requirements

- Every commit must pass formatting (`make fmt`) and tests (`make test-in-docker`).
- **One logical change per commit** — never bundle two concerns (fix vs. feature, refactor vs. behavior change, infrastructure vs. consumer). An "and", "also", or ";" in the subject is a red flag; if a reviewer could approve one half and reject the other, split.
- **Version bump**: Bump the semver `version` in `Skargo.toml` in every code PR (patch = bug fix, minor = feature/behavior change, major = breaking) as part of the PR, not a separate release commit. (Pure docs-only PRs under `docs/` or root `*.md` do not need to touch `Skargo.toml` — touching it triggers a full CI build instead of the docs-only fast path.)

## Commit Ordering

1. **Pinning test commit first (never same-commit with the fix).** Every behavior change — especially every fix — starts with a pinning test in its **own** commit demonstrating the current (pre-change) behavior (annotated with the pre-change `@skjs-expect-error`, or unannotated if currently accepted). The code commit then flips the annotations, making the diff self-explanatory while every commit stays green. Sole exception: the pre-change test crashes the test runner itself (then test and fix may share a commit, with a comment explaining why).
2. **Fixes and infrastructure before dependent features.** Commit fixes/refactors/infrastructure before the feature that builds on them so each commit is self-contained and reviewable in order.

## AI Disclosure

Never mask AI assistance. When AI wrote or co-wrote a change:

- Add a `Co-Authored-By` trailer naming provider, model, version, and (only when actually known — never guess) effort/reasoning setting:

  ```text
  Co-Authored-By: Claude Fable 5 (Anthropic claude-fable-5[1m], effort high) <noreply@anthropic.com>
  ```

- Report the model/settings in effect **when the code was written** (not when later rebased/split/committed). Use one trailer per contributing AI.
- Disclose AI assistance in PR descriptions the same way.

## Documentation & PR Descriptions

- Update `skjs-rules.md` (and `docs/typescript-soundness-holes.md` when relevant) in the same commit or PR when changing what SKJS accepts or rejects. Only document differences from standard TypeScript, with concrete examples.
- Keep PR descriptions concise: summary and motivation only — don't enumerate every changed file.
