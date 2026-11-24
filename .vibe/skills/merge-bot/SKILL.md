---
name: merge-bot
description: >-
  Operate the SKJS merge queue via bin/merge-bot.sh, a thin wrapper around
  Skip's merge bot (../skip/bin/merge-bot.sh). A PR is ready when auto-merge
  is enabled AND its CI is green; red-CI PRs are never touched. Load when the
  user asks to run the merge bot, land or process ready PRs / the merge queue,
  or mentions bin/merge-bot.sh.
---

# merge-bot (skjs)

skjs does not keep its own copy of the merge bot — `bin/merge-bot.sh` here is a
thin wrapper that execs `../skip/bin/merge-bot.sh` (`SKIP_DIR` to override the
skip checkout) with skjs-specific knobs:

- `MERGE_BOT_PATH_EST` — skjs changed-paths CI heuristic (set by the wrapper)
- `MERGE_BOT_REFERENCES_DIR` — this dir; only `references/fix-ci.md` (the skjs
  CI mapping) differs from skip's briefs, everything else falls back to
  `../skip/.vibe/skills/merge-bot/references/`
- state dir `~/.cache/skjs-merge-bot` (derived by skip's bot from the repo name)

**Read the operator manual at `../skip/.vibe/skills/merge-bot/SKILL.md` and
follow it** — readiness rules, the one-PR-at-a-time loop, the
prepare/push/wait steps, fixer sub-agents, and safety rules all live there.
Run every command through this repo's `bin/merge-bot.sh` (e.g.
`bin/merge-bot.sh pick`, `bin/merge-bot.sh run`, `bin/merge-bot.sh --selftest`);
arguments are passed straight through to skip's bot.

skjs-specific notes:

- the required check on `main` is `ci/circleci: build` (the single job in
  `.circleci/config.yml`)
- `bin/merge-bot.sh --selftest` runs skip's selftest (needs the skip checkout;
  runs as part of `make check-sh`)
- human overview: AGENTS.md, "Merge bot"
