#!/usr/bin/env bash
#
# merge-bot.sh — thin wrapper around Skip's merge bot (SkipLabs/skip).
#
# skjs always keeps a skip checkout next to this repo (SKIP_DIR, default
# ../skip — the same convention as the Makefile's docker targets), so instead
# of copying the bot we delegate to $SKIP_DIR/bin/merge-bot.sh and override
# only the repo-specific knobs:
#
#   - MERGE_BOT_PATH_EST        skjs changed-paths CI heuristic (below)
#   - MERGE_BOT_REFERENCES_DIR  this repo's .vibe/skills/merge-bot/references/
#                               (only fix-ci.md differs from skip's; the rest
#                               fall back to skip's bundled briefs)
#   - MERGE_BOT_STATE_DIR       ~/.cache/skjs-merge-bot (same value skip's bot
#                               derives from the repo name; set explicitly so
#                               this also works with a pre-reuse skip bot)
#
# Everything else — readiness rules, scan/pick/prepare/push/wait/run, fixer
# sub-agents, --selftest — is skip's bot, unchanged. The merge-bot skill here
# is likewise shared: .vibe/skills/merge-bot/SKILL.md symlinks to skip's.
# See ../skip/HACKING.md ("Merge bot") and ../skip/.vibe/skills/merge-bot/SKILL.md.
#
# Usage: bin/merge-bot.sh [options] <command> [args]   (passed straight through;
# see ../skip/bin/merge-bot.sh --help)
#
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
SKJS_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
SKIP_DIR=${SKIP_DIR:-$SKJS_ROOT/../skip}
BOT="$SKIP_DIR/bin/merge-bot.sh"

if [ ! -x "$BOT" ]; then
    echo "error: skip merge bot not found at $BOT" >&2
    echo "set SKIP_DIR to your skip checkout (default: $SKIP_DIR)" >&2
    exit 1
fi

# skjs changed-paths CI heuristic (jq body for path_est; $p = changed paths).
# Docs-only PRs skip the build in CI (see .circleci/config.yml); src/ changes
# pay for a full build + test suite.
# shellcheck disable=SC2016 # single quotes intentional: jq program, not shell
export MERGE_BOT_PATH_EST=${MERGE_BOT_PATH_EST:-'if ($p | length) == 0 then 600
   elif ($p | all(test("\\.md$|^docs/|^LICENSE|^\\.github/|^\\.circleci/|^CHANGELOG"))) then 120
   elif ($p | any(test("^src/"))) then 1500
   elif ($p | any(test("^tests/|^examples/|^generated-examples/|^scripts/|^bin/|^import-stubs/|^Makefile|^build\\.sk|^Skargo\\.toml|^runtime\\.(cpp|h)$"))) then 900
   else 300 end'}

export MERGE_BOT_REFERENCES_DIR=${MERGE_BOT_REFERENCES_DIR:-$SKJS_ROOT/.vibe/skills/merge-bot/references}

export MERGE_BOT_STATE_DIR=${MERGE_BOT_STATE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/skjs-merge-bot}

exec "$BOT" "$@"
