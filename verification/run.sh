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
  skjs_shutdown
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
  suite_names[$index]="$name"
  suite_pids[$index]=$!
  suite_logs[$index]="$log"
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

source "$REPO/verification/skjs.sh"
# One container for the whole run, started before anything forks.
skjs_start || echo "warning: no shared container; each check will start its own"

# A fixture is a parsed source and the producer's claims for it, under one name.
# Building one is a precondition rather than a test: with no fixture there is
# nothing to run, so a failure here stops the run instead of being counted.
fixture() { # name source-path
  local name="$1" path="$2"
  if ! { node verification/tools/parse-source.mts "$path" > "$WORK/$name.ast" &&
         skjs_check "$path" > "$WORK/$name.claims"; } 2> "$WORK/$name.err"; then
    echo "FAIL: fixture setup for $path"
    cat "$WORK/$name.err"
    exit 1
  fi
}

# Some witnesses exist because SKJS rejects them, so the rejection is the
# fixture and an acceptance is the failure. A status may be named where the
# kind of rejection is itself the point.
rejected_fixture() { # name source-path [expected status]
  local name="$1" path="$2" want="${3:-}"
  node verification/tools/parse-source.mts "$path" > "$WORK/$name.ast" || exit 1
  skjs_check "$path" > "$WORK/$name.claims" 2> "$WORK/$name.err"
  local got=$?
  if [ "$got" -eq 0 ] || { [ -n "$want" ] && [ "$got" -ne "$want" ]; }; then
    echo "FAIL: expected SKJS to reject $path${want:+ with status $want}, got $got"
    cat "$WORK/$name.err"
    exit 1
  fi
}

# The exporter's own probes, exported together. Some are rejected on purpose
# and their claims are still exported, so the status is not the fixture; and
# they may use any TypeScript, so they do not go through the source parser.
SNAPSHOTS=verification/tests/export-snapshots
snapshot_probes() {
  skjs_check "$SNAPSHOTS"/*.ts > "$WORK/snapshots.claims" 2> "$WORK/snapshots.err" || true
}

# The front end is TypeScript and is checked as such: `tsc` over the trusted
# tools and over the reader's own types, under the same strictness the corpus
# is claimed at. A silently-renamed compiler API reads as `undefined` at
# runtime and as an error here.
typecheck() {
  (cd verification/tools && npx tsc -p tsconfig.json &&
   npx tsc -p ../report-viewer/tsconfig.json)
}

if [ "$SUITE" = stateful-source ] || [ "$SUITE" = all ]; then
  run_test "Front-end types" typecheck
  run_test "Source boundaries" node verification/tests/unsupported.mts "$VERIFIER"

  BASE=verification/tests/stateful-source/basic.ts
  CELL_SOURCE=verification/tests/stateful-source/cells.ts
  UNDEFINED_SOURCE=verification/tests/stateful-source/undefined.ts
  CLOSURES=verification/tests/stateful-source/closures.ts
  CALLABLES=verification/tests/callables/unions.ts
  FACTORIES=verification/tests/callables/factories.ts
  CALLABLE_THUNKS=verification/tests/callables/thunks.ts
  CALLABLE_CELLS=verification/tests/callables/cells.ts
  RECEIVER_CALL=verification/tests/callables/receiver-call.ts
  CALLABLE_FIELD=verification/tests/callables/function-field.ts
  CALLABLE_GUARDS=verification/tests/callables/guards.ts
  CALLABLE_ARITY=verification/tests/callables/arity.ts
  CALLABLE_ARGUMENTS=verification/tests/callables/arguments.ts
  CALLBACKS=verification/tests/stateful-source/primitive-callbacks.ts
  COUNTEREXAMPLE=verification/tests/skjs-unsound/captured-refinement.ts
  NEGATION=verification/tests/stateful-source/negation.ts
  LOOP_EXIT=verification/tests/skjs-incomplete/negated-loop-exit.ts
  SINGLETON=verification/tests/skjs-incomplete/singleton-negation.ts
  NULL_TESTS=verification/tests/stateful-source/null-tests.ts
  NULL_GUARD=verification/tests/stateful-source/null-guards.ts
  NULL_EXIT=verification/tests/skjs-incomplete/null-loop-exit.ts
  COMPOUND_STALE=verification/tests/skjs-unsound/compound-write-refinement.ts
  CONTROLS=verification/tests/refinement-controls.ts
  WRITE_REFINED=verification/tests/skjs-incomplete/write-refined-read.ts
  LOOPS=verification/tests/stateful-source/loops.ts
  TRANSFERS=verification/tests/stateful-source/loop-transfers.ts
  PARTIAL=verification/tests/partial-claims.ts
  CELLS=verification/tests/stateful-source/cell-contracts.ts

  # Fixtures are independent and each is dominated by a container start, so
  # they are built at once rather than in turn. Every one writes under its own
  # name, and a failure inside a background build still stops the run.
  building=()
  build() { "$@" & building+=($!); }
  build fixture source "$BASE"
  build fixture cells "$CELL_SOURCE"
  build fixture undefined "$UNDEFINED_SOURCE"
  build fixture closures "$CLOSURES"
  build fixture callables "$CALLABLES"
  build fixture factories "$FACTORIES"
  build fixture callable_thunks "$CALLABLE_THUNKS"
  build fixture callable_cells "$CALLABLE_CELLS"
  build fixture receiver_call "$RECEIVER_CALL"
  build fixture callable_field "$CALLABLE_FIELD"
  build fixture callable_guards "$CALLABLE_GUARDS"
  build fixture callable_arity "$CALLABLE_ARITY"
  build fixture callable_arguments "$CALLABLE_ARGUMENTS"
  build fixture callbacks "$CALLBACKS"
  build fixture counterexample "$COUNTEREXAMPLE"
  build fixture negation "$NEGATION"
  build fixture null-tests "$NULL_TESTS"
  build fixture null-guard "$NULL_GUARD"
  build fixture compound-stale "$COMPOUND_STALE"
  build fixture refinement-controls "$CONTROLS"
  build fixture loops "$LOOPS"
  build fixture transfers "$TRANSFERS"
  build rejected_fixture loop-exit "$LOOP_EXIT"
  build rejected_fixture singleton "$SINGLETON"
  build rejected_fixture null-exit "$NULL_EXIT"
  build rejected_fixture write-refined "$WRITE_REFINED" 2
  build snapshot_probes
  for pid in "${building[@]}"; do wait "$pid" || exit 1; done

  # The partial export must not change what ordinary checking reports: same
  # status, same diagnostics, with claims recovered only under --keep-going.
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
  if ! skjs_check "$CELLS" > "$WORK/cell.claims" 2> "$WORK/cell.err"; then
    echo "FAIL: cell contract export setup"; cat "$WORK/cell.err"; exit 1
  fi

  run_test "Source claims and certificates" node verification/tests/stateful-source.mts        "$WORK/source.ast" "$WORK/source.claims" "$BASE" "$VERIFIER"
  run_test "Mutable cells" node verification/tests/stateful-cells.mts        "$WORK/cells.ast" "$WORK/cells.claims" "$CELL_SOURCE" "$VERIFIER"
  run_test "Undefined values and contracts" node verification/tests/undefined.mts        "$WORK/undefined.ast" "$WORK/undefined.claims" "$UNDEFINED_SOURCE" "$VERIFIER"
  run_test "Closures" node verification/tests/stateful-closures.mts        "$WORK/closures.ast" "$WORK/closures.claims" "$CLOSURES" "$VERIFIER"
  run_test "Callables" node verification/tests/callables.mts "$WORK/callables.ast" "$WORK/callables.claims" "$CALLABLES" "$VERIFIER"
  run_test "Local arrow receiver calls" node verification/tests/receiver-call.mts "$WORK/receiver_call.ast" "$WORK/receiver_call.claims" "$RECEIVER_CALL" "$VERIFIER"
  run_test "Initialized callable field" node verification/tests/function-field.mts "$WORK/callable_field.ast" "$WORK/callable_field.claims" "$CALLABLE_FIELD" "$VERIFIER"
  run_test "Callable shape guards" node verification/tests/callable-guards.mts "$WORK/callable_guards.ast" "$WORK/callable_guards.claims" "$CALLABLE_GUARDS" "$VERIFIER"
  run_test "Function/object receiver boundary" node verification/tests/call-objects.mts
  run_test "Call argument order" node verification/tests/callable-arity.mts "$WORK/callable_arity.ast" "$WORK/callable_arity.claims" "$CALLABLE_ARITY" "$VERIFIER"
  run_test "Callable thunks" node verification/tests/callable-thunks.mts "$WORK/callable_thunks.ast" "$WORK/callable_thunks.claims" "$CALLABLE_THUNKS" "$VERIFIER"
  run_test "Callable cells" node verification/tests/callable-cells.mts "$WORK/callable_cells.ast" "$WORK/callable_cells.claims" "$CALLABLE_CELLS" "$VERIFIER"
  run_test "Callable arguments" node verification/tests/callable-arguments.mts "$WORK/callable_arguments.ast" "$WORK/callable_arguments.claims" "$CALLABLE_ARGUMENTS" "$VERIFIER"
  run_test "Callable factories" node verification/tests/callable-factories.mts "$WORK/factories.ast" "$WORK/factories.claims" "$FACTORIES" "$VERIFIER"
  run_test "Primitive callbacks and unsoundness witness" node verification/tests/primitive-callbacks.mts        "$WORK/callbacks.ast" "$WORK/callbacks.claims" "$CALLBACKS" "$VERIFIER"        "$WORK/counterexample.ast" "$WORK/counterexample.claims" "$COUNTEREXAMPLE"
  run_test "Negation and claim repair" node verification/tests/negation.mts        "$WORK/negation.ast" "$WORK/negation.claims" "$NEGATION" "$VERIFIER"        "$WORK/loop-exit.ast" "$WORK/loop-exit.claims" "$LOOP_EXIT"        "$WORK/singleton.ast" "$WORK/singleton.claims" "$SINGLETON"
  run_test "Null predicates" node verification/tests/null-tests.mts        "$WORK/null-tests.ast" "$WORK/null-tests.claims" "$NULL_TESTS" "$VERIFIER"        "$WORK/null-guard.ast" "$WORK/null-guard.claims" "$NULL_GUARD"        "$WORK/null-exit.ast" "$WORK/null-exit.claims" "$NULL_EXIT"        "$WORK/compound-stale.ast" "$WORK/compound-stale.claims" "$COMPOUND_STALE"
  run_test "Refinement witness audit" node verification/tests/refinement-witnesses.mts "$VERIFIER"        "$WORK/counterexample.ast" "$WORK/counterexample.claims" "$COUNTEREXAMPLE"        "$WORK/compound-stale.ast" "$WORK/compound-stale.claims" "$COMPOUND_STALE"        "$WORK/refinement-controls.ast" "$WORK/refinement-controls.claims" "$CONTROLS"
  run_test "Write observations and producer witnesses" node verification/tests/write-observations.mts        "$WORK/write-refined.ast" "$WORK/write-refined.claims" "$WRITE_REFINED"        "$WORK/compound-stale.ast" "$WORK/compound-stale.claims" "$COMPOUND_STALE" "$VERIFIER"
  run_test "While loops" node verification/tests/stateful-loops.mts        "$WORK/loops.ast" "$WORK/loops.claims" "$LOOPS" "$VERIFIER"
  run_test "Break and continue" node verification/tests/stateful-loop-transfers.mts        "$WORK/transfers.ast" "$WORK/transfers.claims" "$TRANSFERS" "$VERIFIER"
  run_test "Producer-neutral claims" node verification/tests/source-claims.mts "$VERIFIER"
  run_test "Source heap assertions" node verification/tests/source-heap-claims.mts "$VERIFIER"
  run_test "Claim export" node verification/tests/source-claim-export.mts        "$WORK/closures.claims" "$CLOSURES" "$WORK/partial.claims" "$PARTIAL"        "$WORK/recovery.claims" "$VERIFIER" "$WORK/partial.err"
  run_test "Partial collection" node verification/tests/partial-claims.mts        "$WORK/partial.claims" "$WORK/recovery.claims" "$PARTIAL" "$VERIFIER" "$WORK/partial.err"
  run_test "Annotated source reports" node verification/tests/annotated-source.mts        "$WORK/closures.claims" "$CLOSURES" "$VERIFIER"
  run_test "Obligation diagnostics" node verification/tests/obligation-diagnostics.mts "$VERIFIER"
  run_test "Report viewer" node verification/tests/report-viewer.mts
  run_test "Candidate editing" node verification/tests/candidate-editor.mts "$WORK/closures.claims"
  run_test "Export snapshots" node verification/tests/export-snapshots.mts "$WORK/snapshots.claims" "$SNAPSHOTS"
  run_test "TypeScript claims" node verification/tests/tsc-claims.mts "$VERIFIER"
  # The drafts kept beside corpus sources: still about those sources, and still
  # verifying. A stale one is ignored by the reader and would go unnoticed here.
  run_test "Kept drafts" node verification/tests/kept-drafts.mts
  run_test "Cell contract export" "$REPO/verification/lean/.lake/build/bin/cell_claim_tests"        "$WORK/cell.claims" "$CELLS"
  report_tests
fi

completed=1
[ "$failed" -eq 0 ]
