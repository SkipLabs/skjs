#!/usr/bin/env bash
# Report how much of a corpus the source pipeline verifies, one row per
# function. Usage: verification/census.sh [corpus.json] [--update]
#
# Unlike run.sh this asserts nothing about the corpus: a refusal is a reported
# outcome. The exit status is about the census itself — a baseline that moved,
# or a certificate the consumer rejected — never about how much verified.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO" || exit 1

CORPUS="${1:-verification/corpus/repair-work.json}"
case "$CORPUS" in --*) CORPUS=verification/corpus/repair-work.json ;; *) shift || true ;; esac
UPDATE=()
for arg in "$@"; do [ "$arg" = --update ] && UPDATE=(--update); done

VERIFIER="$REPO/verification/lean/.lake/build/bin/verifier"
[ -x "$VERIFIER" ] || { echo "no verifier: build it with verification/run.sh --build"; exit 1; }
NAME="$(node -p "require('./$CORPUS').name")"
BASELINE="verification/corpus/$NAME.census"

WORK="$(mktemp -d)"
# Under the repo so the container mount and the strict verification project
# both see the extracted sources.
DIR="$(mktemp -d verification/tests/.census.XXXXXX)"
source "$REPO/verification/skjs.sh"
finish() { rm -rf "$WORK" "$DIR"; skjs_shutdown; }
trap finish EXIT

node verification/tools/census.mts --extract "$CORPUS" "$DIR" || exit 1
skjs_start || echo "warning: no shared container; each check will start its own"
# Corpus sources are error tests, so a nonzero status is expected and the
# claims are what matter. They are exported in one invocation, not per file.
skjs_check "$DIR"/*.ts > "$WORK/census.claims" 2> "$WORK/census.err" || true
if [ ! -s "$WORK/census.claims" ]; then
  echo "FAIL: no claims exported"; cat "$WORK/census.err"; exit 1
fi
# The producer's own diagnostics go with the claims: a function it rejected
# states nothing to check, and is not a boundary of the verified fragment.
node verification/tools/census.mts --report "$CORPUS" "$DIR" \
  "$WORK/census.claims" "$VERIFIER" --producer-errors "$WORK/census.err" \
  --baseline "$BASELINE" "${UPDATE[@]+"${UPDATE[@]}"}"
