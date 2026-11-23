#!/usr/bin/env bash
#
# ci_classify_changes.sh — classify a branch's diff against main so CircleCI
# can skip the expensive steps (Skip clone, skargo build, test suite) when
# they cannot change the outcome. Prints exactly one line:
#
#   docs-only   every changed file is documentation (docs/, root *.md, LICENSE)
#   infra-only  every changed file is docs or repo infra that no step of
#               `skargo build` / `make test` reads (bin/, .vibe/, .github/,
#               scripts/, devtools/, npm/, Makefile, ...)
#   full        anything else — the fail-safe default
#
# .circleci/config.yml halts the build job *green* on docs-only (before the
# cheap checks) and on infra-only (after `make check-fmt` / `make check-sh`,
# before the Skip clone), so the required `ci/circleci: build` check still
# reports and the PR stays mergeable — a path-filtering/dynamic-config setup
# would drop the job entirely and leave the required check pending forever.
#
# Fail safe: any uncertainty (no merge base, git error, empty diff,
# unrecognized path, script error) yields `full`, so a change we cannot prove
# harmless always gets the clone + build + tests.
#
# Usage:
#   bin/ci_classify_changes.sh             print the change class (one line)
#   bin/ci_classify_changes.sh --selftest  unit-test the classifier (no git
#                                          needed); runs as part of
#                                          `make check-sh`
#
# This script and bin/ci_build_cache.sh are themselves excluded from the
# infra list below: the CI job runs both, so a change to either gets a full
# build.

set -euo pipefail

# --- path classification (pure functions; unit-tested by --selftest) ----------

# Documentation: no build or test reads these. Only root-level *.md count —
# a *.md nested under tests/ or import-stubs/ can trip the test harness's
# unexpected-non-ts-file invariant, so it must not classify as docs.
is_docs_path() {
  case "$1" in
    docs/*|LICENSE) return 0 ;;
    *.md) case "$1" in */*) return 1 ;; *) return 0 ;; esac ;;
    *) return 1 ;;
  esac
}

# Repo infra: no step of `skargo build` / `make test` reads these paths. The
# build/test inputs are src/, tests/, examples/, import-stubs/,
# generated-examples/, experiment/, Skargo.toml, build.sk, runtime.* and the
# ../skip path deps (see Makefile and bin/ci_build_cache.sh). Conservative by
# design: anything that could affect the dev binaries or test results is NOT
# listed here and therefore forces a full build. Makefile is listed because
# infra-only PRs still run the cheap `make check-fmt` / `make check-sh`
# targets (which fail on a broken Makefile); only the clone/build/tests are
# skipped, which is the point.
is_infra_path() {
  case "$1" in
    # Read by the CI job itself — validate changes to them with a full build.
    bin/ci_build_cache.sh|bin/ci_classify_changes.sh) return 1 ;;
    .circleci/*|.gitattributes) return 1 ;;
    bin/*|.vibe/*|.github/*|.vscode/*|.claude/*) return 0 ;;
    scripts/*|devtools/*|npm/*) return 0 ;;
    Makefile|package.json|package-lock.json|.prettierrc|.prettierignore|.gitignore) return 0 ;;
    *) return 1 ;;
  esac
}

# Read changed paths on stdin; print docs-only | infra-only | full.
classify_list() {
  local f n=0 saw_infra=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    n=$((n + 1))
    if is_docs_path "$f"; then continue; fi
    if is_infra_path "$f"; then saw_infra=1; continue; fi
    echo full
    return 0
  done
  # An empty diff proves nothing: build.
  if [ "$n" -eq 0 ]; then echo full; return 0; fi
  if [ "$saw_infra" = 1 ]; then echo infra-only; else echo docs-only; fi
}

# --- diff against main ---------------------------------------------------------

classify_diff() {
  # main and tags always get the full build.
  if [ "${CIRCLE_BRANCH:-}" = "main" ] || [ -n "${CIRCLE_TAG:-}" ]; then
    echo full
    return 0
  fi
  # Guarantee full history so the merge base is exact. --unshallow errors on
  # an already-complete clone, hence the `|| true`.
  git fetch --quiet --unshallow origin 2>/dev/null || true
  git fetch --quiet origin main || { echo full; return 0; }
  local base
  base=$(git merge-base HEAD FETCH_HEAD 2>/dev/null) || { echo full; return 0; }
  git diff --name-only "$base" HEAD 2>/dev/null | classify_list
}

classify() {
  local class
  class=$(classify_diff) || class=full
  case "$class" in
    docs-only|infra-only|full) ;;
    *) class=full ;;
  esac
  printf '%s\n' "$class"
}

# --- selftest ------------------------------------------------------------------

cmd_selftest() {
  local fails=0
  check() { # check <name> <expected> <files...>
    local name=$1 expected=$2 got
    shift 2
    got=$(printf '%s\n' "$@" | classify_list)
    if [ "$got" = "$expected" ]; then
      echo "ok - $name"
    else
      echo "FAIL - $name: expected [$expected] got [$got] for: $*"
      fails=$((fails + 1))
    fi
  }

  # docs-only: docs/, root *.md, LICENSE
  check "docs only" docs-only docs/setup.md AGENTS.md skjs-rules.md LICENSE README.md
  # a nested *.md is not docs (tests/expect-error/*.md would trip the test
  # harness's non-ts-file invariant); generated-examples/ is not infra either
  check "nested md is full" full tests/expect-error/notes.md
  check "generated-examples md is full" full generated-examples/README.md

  # infra-only: PR #1103's exact file list (the merge bot)
  check "infra-only (#1103 merge bot)" infra-only \
    .vibe/skills/merge-bot/SKILL.md \
    .vibe/skills/merge-bot/references/fix-ci.md \
    .vibe/skills/merge-bot/references/fix-conflicts.md \
    AGENTS.md Makefile bin/merge-bot.sh
  check "infra-only assorted" infra-only \
    bin/new-tool.sh bin/claude_hooks/format_file.sh bin/git_hooks/check_format.sh \
    scripts/survey-projects.sh devtools/copy-ts-tests.sh npm/package.json \
    .github/workflows/arm64-test.yml .github/dependabot.yml .github/ISSUE_TEMPLATE/crash.md \
    .vibe/skills/other/SKILL.md .vscode/settings.json .claude/settings.json \
    Makefile package.json package-lock.json .gitignore .prettierrc .prettierignore
  check "docs+infra mix" infra-only docs/testing.md Makefile bin/merge-bot.sh

  # full: build/test inputs and CI-owned files
  check "src is full" full src/TType.sk
  check "tests are full" full tests/expect-error/eqeqeq.ts
  check "examples are full" full examples/src/app.ts
  check "import-stubs are full" full import-stubs/node/fs.d.ts
  check "build inputs are full" full Skargo.toml build.sk runtime.cpp runtime.h
  check "generated-examples are full" full generated-examples/blog-post/main.ts
  check "experiment is full" full experiment/helpers-stub-additions.ts
  check "circleci config is full" full .circleci/config.yml
  check "ci scripts are full" full bin/ci_build_cache.sh bin/ci_classify_changes.sh
  check "gitattributes is full" full .gitattributes
  check "infra+code mix is full" full Makefile src/TType.sk
  check "docs+ci-script mix is full" full AGENTS.md bin/ci_build_cache.sh

  # empty diff: fail safe to full
  check "empty diff is full" full

  if [ "$fails" -eq 0 ]; then
    echo "selftest: all passed"
  else
    echo "selftest: $fails failure(s)"
    exit 1
  fi
}

case "${1:-}" in
  --selftest) cmd_selftest ;;
  "") classify ;;
  *)
    echo "usage: $0 [--selftest]" >&2
    exit 2
    ;;
esac
