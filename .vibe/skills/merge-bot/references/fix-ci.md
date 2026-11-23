# CI-fixer brief — PR #__PR__ (__PR_URL__)

You are a sub-agent spawned by the merge bot (`bin/merge-bot.sh`). The bot
rebased PR #__PR__ (branch `__BRANCH__`) onto `origin/__BASE__` in repo
`__REPO__` and pushed it; the required CI then failed on the new head. Your job
is to make the CI green again. Read `AGENTS.md` at the repo root first and
follow it.

## Situation

- Your worktree is `__WORKTREE__` (a `git worktree` of the bot's dedicated
  clone, currently at the rebased+pushed head of the PR, clean).
- Failing checks on the pushed head:

  ```
  __FAILED_CHECKS__
  ```

## Task

1. `cd __WORKTREE__` and create a local branch, e.g.
   `git switch -c mergebot-fix-pr-__PR__`.
2. Reproduce the failures locally with the narrowest relevant command. skjs CI
   is a single `ci/circleci: build` job (.circleci/config.yml) that runs
   `make check-fmt`, `make check-sh`, then `make test` inside the Skip docker
   image. Open the failing check's CircleCI URL in `__FAILED_CHECKS__`, read
   which step failed, and map it to the narrowest local equivalent:
   - "Check code is formatted" → `make fmt`, then re-verify with `make check-fmt`
   - "Check shell scripts" → `shellcheck <file>` (and `bin/merge-bot.sh --selftest`
     for the bot script itself), via `make check-sh`
   - "Test" (skargo build/test failures) → `make check-in-docker` /
     `make test-in-docker`, or narrower: `make check-file-in-docker FILE=<repro.ts>`
     for a single-file repro
   Do not run the full CI matrix locally; fix the failing step only.
3. Fix the root cause with the smallest change that keeps the PR's intent.
   The rebase itself may have introduced a semantic clash with `__BASE__` —
   prefer adapting the PR's change to the new `__BASE__` over reverting it.
4. Commit the fix (keep authorship conventions; add the
   `Co-Authored-By: Mistral Vibe <vibe@mistral.ai>` trailer per AGENTS.md).
5. Write the verdict file `__VERDICT_FILE__` whose FIRST LINE is exactly one
   of:
   - `OK` — CI failures fixed, fix committed on top of the pushed head,
     worktree clean.
   - `NONTRIVIAL: <one-paragraph reason a human must decide>` — in this case
     leave the worktree clean (commit nothing or reset back to the pushed
     head).

## Hard rules

- Never push, never force-push, never touch `__BASE__`/main. The bot pushes
  your committed HEAD back to `__BRANCH__` if the verdict is `OK`.
- Never commit build artifacts or caches (see the don't list in AGENTS.md).
- Do not modify `.github/`, `.circleci/`, branch protection, `bin/merge-bot.sh`,
  or this file.
- Do not "fix" CI by weakening tests, deleting assertions, or editing CI
  config to skip the failing job — fix the code.
