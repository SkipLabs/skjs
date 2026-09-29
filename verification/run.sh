#!/usr/bin/env bash
# Build and exercise the parser -> OCaml producer -> Lean pipeline and the
# checks around it: front-end types, JSON field names, documents, the rule
# inventory and the source boundaries.
# Usage: verification/run.sh [--build] [--verbose]
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO" || exit 1

BUILD=0
VERBOSE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --build) BUILD=1; shift ;;
    --verbose) VERBOSE=1; shift ;;
    *) echo "Unknown argument: $1"; exit 2 ;;
  esac
done

WORK="$(mktemp -d)"
passed=0
failed=0
completed=0
build_status="not requested"
started_at=$SECONDS

# Match the example report; preserve readable plain text in logs and NO_COLOR.
status_line() {
  local color="$1"
  shift
  if [ -t 1 ] && [ "${TERM:-}" != dumb ] && [ -z "${NO_COLOR:-}" ]; then
    printf '\033[%sm%s\033[0m\n' "$color" "$*"
  else
    printf '%s\n' "$*"
  fi
}

# Count test executables, not their differently formatted internal assertions.
# An early setup/build failure must still produce a failed, incomplete summary.
finish() {
  local status=$?
  echo
  if [ "$status" -eq 0 ]; then
    status_line 32 "✓ Pipeline tests: PASS"
  else
    status_line 31 "✗ Pipeline tests: FAIL"
  fi
  echo "  Lean build: $build_status"
  echo "  Test suites: $passed passed, $failed failed"
  if [ "$completed" -eq 0 ]; then
    status_line 33 "  ⚠ Run stopped early; remaining suites were not run."
  fi
  echo "  Elapsed: $((SECONDS - started_at))s"
  rm -rf "$WORK"
}
trap finish EXIT

# Suites are independent, so they start together and are reported in the order
# they were written. Output is buffered per suite rather than interleaved, and
# every suite runs: a failure is counted and reported with the rest instead of
# ending the run, which is what the summary is for.
suite_names=()
suite_pids=()
suite_logs=()
run_test() {
  local name="$1"
  shift
  local index=${#suite_names[@]}
  local log="$WORK/suite-$index.out"
  ( "$@" ) > "$log" 2>&1 &
  suite_names[index]="$name"
  suite_pids[index]=$!
  suite_logs[index]="$log"
}

report_tests() {
  local index status
  for ((index = 0; index < ${#suite_names[@]}; index++)); do
    printf '\n%s\n' "${suite_names[$index]}"
    wait "${suite_pids[$index]}"
    status=$?
    cat "${suite_logs[$index]}"
    if [ "$status" -eq 0 ]; then
      passed=$((passed + 1))
      status_line 32 "✓ ${suite_names[$index]}"
    else
      failed=$((failed + 1))
      status_line 31 "✗ ${suite_names[$index]}"
    fi
  done
}

if [ "$BUILD" -eq 1 ]; then
  build_status="failed"
  echo "Building verifier..."
  if (cd verification/lean && lake build) > "$WORK/build.out" 2>&1; then
    build_status="passed"
    [ "$VERBOSE" -eq 0 ] || cat "$WORK/build.out"
  else
    echo "FAIL: verifier build"
    cat "$WORK/build.out"
    exit 1
  fi
fi

# The front end is TypeScript and is checked as such: `tsc` over the trusted
# tools and over the reader's own types, under the same strictness the corpus
# is claimed at. A silently-renamed compiler API reads as `undefined` at
# runtime and as an error here.
typecheck() {
  (cd verification/tools && npx tsc -p tsconfig.json &&
   npx tsc -p ../report-viewer/tsconfig.json)
}

run_test "Front-end types" typecheck
run_test "JSON field names agree (TS, Lean, OCaml)" node verification/tests/json-field-names.mts
run_test "Documents: links, math" node verification/tests/docs.mts
run_test "OCaml producer" bash -c 'dune build --root verification/ocaml-producer && dune runtest --root verification/ocaml-producer && node verification/ocaml-producer/test.mts'
run_test "Rule inventory" node verification/tests/rule-inventory.mts
run_test "Source boundaries" node verification/tests/unsupported.mts

report_tests

completed=1
[ "$failed" -eq 0 ]
