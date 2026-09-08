#!/usr/bin/env bash
# Build and exercise the current source adapter, certificate consumer and reports.
# Usage: verification/run.sh [--build] [--verbose] [--skjs BIN] [--suite stateful-source|all]
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"

SKJS_BIN="${SKJS_BIN:-target/host/dev/skjs}"
BUILD=0
VERBOSE=0
SUITE=all
while [ $# -gt 0 ]; do
  case "$1" in
    --build) BUILD=1; shift ;;
    --verbose) VERBOSE=1; shift ;;
    --suite) SUITE="${2:-}"; shift; [ $# -eq 0 ] || shift ;;
    --skjs) SKJS_BIN="$2"; shift 2 ;;
    *) echo "Unknown argument: $1"; exit 2 ;;
  esac
done
case "$SUITE" in
  stateful-source|all) ;;
  *) echo "Unknown suite '$SUITE': use stateful-source or all"; exit 2 ;;
esac

VERIFIER="$REPO/verification/lean/.lake/build/bin/verifier"
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

run_test() {
  local name="$1"
  shift
  printf '\n%s\n' "$name"
  if "$@"; then
    passed=$((passed + 1))
    status_line 32 "✓ $name"
  else
    failed=$((failed + 1))
    status_line 31 "✗ $name"
    return 1
  fi
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

source "$REPO/verification/skjs.sh"

if [ "$SUITE" = stateful-source ] || [ "$SUITE" = all ]; then
  if ! run_test "Source boundaries" node verification/tests/unsupported.js "$VERIFIER"; then exit 1; fi
  BASE="verification/tests/stateful-source/basic.ts"
  if ! { node verification/tools/parse-source.js "$BASE" > "$WORK/source.ast" &&
         skjs_check "$BASE" > "$WORK/source.claims"; } 2> "$WORK/source.setup.err"; then
    echo "FAIL: stateful source test setup"
    cat "$WORK/source.setup.err"
    exit 1
  fi
  run_test "Source claims and certificates" node verification/tests/stateful-source.js "$WORK/source.ast" "$WORK/source.claims" \
       "$BASE" "$VERIFIER"
  CELL_SOURCE="verification/tests/stateful-source/cells.ts"
  if ! { node verification/tools/parse-source.js "$CELL_SOURCE" > "$WORK/cells.ast" &&
         skjs_check "$CELL_SOURCE" > "$WORK/cells.claims"; } 2> "$WORK/cells.setup.err"; then
    echo "FAIL: cell source test setup"
    cat "$WORK/cells.setup.err"
    exit 1
  fi
  run_test "Mutable cells" node verification/tests/stateful-cells.js "$WORK/cells.ast" "$WORK/cells.claims" \
       "$CELL_SOURCE" "$VERIFIER"
  CLOSURES="verification/tests/stateful-source/closures.ts"
  if ! { node verification/tools/parse-source.js "$CLOSURES" > "$WORK/closures.ast" &&
         skjs_check "$CLOSURES" > "$WORK/closures.claims"; } 2> "$WORK/closures.setup.err"; then
    echo "FAIL: closure source test setup"
    cat "$WORK/closures.setup.err"
    exit 1
  fi
  run_test "Closures" node verification/tests/stateful-closures.js "$WORK/closures.ast" "$WORK/closures.claims" \
       "$CLOSURES" "$VERIFIER"
  CALLBACKS="verification/tests/stateful-source/primitive-callbacks.ts"
  COUNTEREXAMPLE="verification/tests/skjs-unsound/captured-refinement.ts"
  for pair in "$CALLBACKS:callbacks" "$COUNTEREXAMPLE:counterexample"; do
    source_file="${pair%:*}"; fixture="${pair##*:}"
    if ! { node verification/tools/parse-source.js "$source_file" > "$WORK/$fixture.ast" &&
           skjs_check "$source_file" > "$WORK/$fixture.claims"; } 2> "$WORK/$fixture.err"; then
      echo "FAIL: callback fixture setup"; cat "$WORK/$fixture.err"; exit 1
    fi
  done
  if ! run_test "Primitive callbacks and unsoundness witness" node verification/tests/primitive-callbacks.js "$WORK/callbacks.ast" "$WORK/callbacks.claims" "$CALLBACKS" "$VERIFIER" \
       "$WORK/counterexample.ast" "$WORK/counterexample.claims" "$COUNTEREXAMPLE"; then exit 1; fi
  NEGATION="verification/tests/stateful-source/negation.ts"
  if ! { node verification/tools/parse-source.js "$NEGATION" > "$WORK/negation.ast" &&
         skjs_check "$NEGATION" > "$WORK/negation.claims"; } 2> "$WORK/negation.err"; then
    echo "FAIL: negation fixture setup"; cat "$WORK/negation.err"; exit 1
  fi
  LOOP_EXIT="verification/tests/skjs-incomplete/negated-loop-exit.ts"
  if ! node verification/tools/parse-source.js "$LOOP_EXIT" > "$WORK/loop-exit.ast"; then exit 1; fi
  if skjs_check "$LOOP_EXIT" > "$WORK/loop-exit.claims" 2> "$WORK/loop-exit.err"; then
    echo "FAIL: SKJS unexpectedly accepts the loop-exit incompleteness witness"; exit 1
  fi
  SINGLETON="verification/tests/skjs-incomplete/singleton-negation.ts"
  if ! node verification/tools/parse-source.js "$SINGLETON" > "$WORK/singleton.ast"; then exit 1; fi
  if skjs_check "$SINGLETON" > "$WORK/singleton.claims" 2> "$WORK/singleton.err"; then
    echo "FAIL: SKJS unexpectedly accepts the singleton-negation witness"; exit 1
  fi
  if ! run_test "Negation and claim repair" node verification/tests/negation.js "$WORK/negation.ast" "$WORK/negation.claims" "$NEGATION" "$VERIFIER" \
       "$WORK/loop-exit.ast" "$WORK/loop-exit.claims" "$LOOP_EXIT" \
       "$WORK/singleton.ast" "$WORK/singleton.claims" "$SINGLETON"; then exit 1; fi
  NULL_TESTS="verification/tests/stateful-source/null-tests.ts"
  NULL_GUARD="verification/tests/unsupported/null-guard.ts"
  for pair in "$NULL_TESTS:null-tests" "$NULL_GUARD:null-guard"; do
    source_file="${pair%:*}"; fixture="${pair##*:}"
    if ! { node verification/tools/parse-source.js "$source_file" > "$WORK/$fixture.ast" &&
           skjs_check "$source_file" > "$WORK/$fixture.claims"; } 2> "$WORK/$fixture.err"; then
      echo "FAIL: null-test fixture setup"; cat "$WORK/$fixture.err"; exit 1
    fi
  done
  if ! run_test "Null predicates" node verification/tests/null-tests.js "$WORK/null-tests.ast" "$WORK/null-tests.claims" "$NULL_TESTS" "$VERIFIER" \
       "$WORK/null-guard.ast" "$WORK/null-guard.claims" "$NULL_GUARD"; then exit 1; fi
  LOOPS="verification/tests/stateful-source/loops.ts"
  if ! { node verification/tools/parse-source.js "$LOOPS" > "$WORK/loops.ast" &&
         skjs_check "$LOOPS" > "$WORK/loops.claims"; } 2> "$WORK/loops.setup.err"; then
    echo "FAIL: loop source test setup"; cat "$WORK/loops.setup.err"; exit 1
  fi
  if ! run_test "While loops" node verification/tests/stateful-loops.js "$WORK/loops.ast" "$WORK/loops.claims" "$LOOPS" "$VERIFIER"; then exit 1; fi
  TRANSFERS="verification/tests/stateful-source/loop-transfers.ts"
  if ! { node verification/tools/parse-source.js "$TRANSFERS" > "$WORK/transfers.ast" &&
         skjs_check "$TRANSFERS" > "$WORK/transfers.claims"; } 2> "$WORK/transfers.setup.err"; then
    echo "FAIL: loop transfer setup"; cat "$WORK/transfers.setup.err"; exit 1
  fi
  if ! run_test "Break and continue" node verification/tests/stateful-loop-transfers.js "$WORK/transfers.ast" "$WORK/transfers.claims" "$TRANSFERS" "$VERIFIER"; then exit 1; fi
  if ! run_test "Producer-neutral claims" node verification/tests/source-claims.js "$VERIFIER"; then exit 1; fi
  PARTIAL=verification/tests/partial-claims.ts
  skjs_run "$PARTIAL" > "$WORK/partial.plain" 2> "$WORK/partial.plain.err"
  plain_status=$?
  skjs_check "$PARTIAL" > "$WORK/partial.claims" 2> "$WORK/partial.err"
  partial_status=$?
  skjs_run --emit-skjs-type-claims --keep-going "$PARTIAL" > "$WORK/recovery.claims" 2> "$WORK/recovery.err"
  recovery_status=$?
  if [ "$plain_status" -eq 0 ] || [ "$plain_status" -ne "$partial_status" ] || [ "$recovery_status" -eq 0 ] ||
     ! cmp -s "$WORK/partial.plain.err" "$WORK/partial.err"; then
    echo "FAIL: partial export changed ordinary diagnostics or exit status"; exit 1
  fi
  if ! run_test "Claim export" node verification/tests/source-claim-export.js "$WORK/closures.claims" "$CLOSURES" "$WORK/partial.claims" "$PARTIAL" "$WORK/recovery.claims" "$VERIFIER" "$WORK/partial.err"; then exit 1; fi
  if ! run_test "Partial collection" node verification/tests/partial-claims.js "$WORK/partial.claims" "$WORK/recovery.claims" "$PARTIAL" "$VERIFIER" "$WORK/partial.err"; then
    exit 1
  fi
  run_test "Annotated source reports" node verification/tests/annotated-source.js "$WORK/closures.claims" "$CLOSURES" "$VERIFIER"
  run_test "Report viewer" node verification/tests/report-viewer.js
  run_test "Candidate editing" node verification/tests/candidate-editor.js "$WORK/closures.claims"
  CELLS="verification/tests/stateful-source/cell-contracts.ts"
  if ! skjs_check "$CELLS" > "$WORK/cell.claims" 2> "$WORK/cell.setup.err"; then
    echo "FAIL: cell contract export setup"
    cat "$WORK/cell.setup.err"
    exit 1
  fi
  run_test "Cell contract export" "$REPO/verification/lean/.lake/build/bin/cell_claim_tests" "$WORK/cell.claims" "$CELLS"

fi

completed=1
[ "$failed" -eq 0 ]
