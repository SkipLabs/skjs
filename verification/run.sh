#!/usr/bin/env bash
#
# The verification harness (verification/DESIGN.md, stage 0).
#
# For every program under verification/tests/programs it runs the four stages of the
# pipeline and checks the outcome against the directory the program lives in:
#
#   accept/         SKJS accepts it AND its claims check
#   reject/         SKJS rejects it (an ordinary type error)
#   outside/        the trusted front end rejects it (the fragment gate)
#   known-unsound/  SKJS accepts it but its claims do NOT check
#
# Stage 1  trusted front end   verification/tools/parse-source.js  (TypeScript API)
# Stage 2  untrusted checker   skjs check --emit-skjs-type-claims
# Stage 3  trusted checker     verification/lean/.lake/build/bin/verifier
# Stage 4  runtime agreement   verification/tools/runtime-check.js  (Node)
#
# The claims suite separately tests the verifier's input validation.
# It uses a real SKJS claim set as a fixture, then alters it in JavaScript.
#
# Usage: verification/run.sh [--build] [--verbose] [--suite programs|claims|stateful-source|all] [--skjs BIN] [filter]
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"

SKJS_BIN="target/host/dev/skjs"
FILTER=""
BUILD=0
VERBOSE=0
SUITE=programs
while [ $# -gt 0 ]; do
  case "$1" in
    --build) BUILD=1; shift ;;
    --verbose) VERBOSE=1; shift ;;
    --suite) SUITE="${2:-}"; shift; [ $# -eq 0 ] || shift ;;
    --skjs) SKJS_BIN="$2"; shift 2 ;;
    *) FILTER="$1"; shift ;;
  esac
done
case "$SUITE" in
  programs|claims|stateful-source|all) ;;
  *) echo "Unknown suite '$SUITE': use programs, claims, stateful-source, or all"; exit 2 ;;
esac
if [ -n "$FILTER" ] && [ "$SUITE" != programs ]; then
  echo "A filename filter is only supported with the programs suite"
  exit 2
fi

DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"
SKIP_DIR="${SKIP_DIR:-$REPO/../skip}"
VERIFIER="$REPO/verification/lean/.lake/build/bin/verifier"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

if [ "$BUILD" -eq 1 ]; then
  echo "Building verifier..."
  if (cd verification/lean && lake build) > "$WORK/build.out" 2>&1; then
    [ "$VERBOSE" -eq 0 ] || cat "$WORK/build.out"
  else
    echo "FAIL: verifier build"
    cat "$WORK/build.out"
    exit 1
  fi
fi

skjs_run() { # CLI options, then repo-relative source path
  if [ -n "${DEVCONTAINER:-}" ]; then
    "$SKJS_BIN" check --import-stubs import-stubs --truthiness boolean \
      "$@"
  else
    docker run --rm -v "$REPO:/work/skjs" -v "$SKIP_DIR:/work/skip" \
      -w /work/skjs "$DOCKER_IMAGE" \
      "$SKJS_BIN" check --import-stubs import-stubs --truthiness boolean \
      "$@"
  fi
}

skjs_check() { skjs_run --emit-skjs-type-claims "$1"; }

pass=0; fail=0
report() { # $1 = OK|FAIL, $2 = file, $3 = detail
  if [ "$1" = "OK" ]; then
    pass=$((pass + 1))
    case "$kind" in
      accept) echo "verified" ;;
      reject) echo "rejected by SKJS (expected)" ;;
      outside) echo "outside fragment (expected)" ;;
      known-unsound) echo "unsound result caught (expected)" ;;
    esac
    [ "$VERBOSE" -eq 0 ] || printf '    %s\n' "$3"
  else
    fail=$((fail + 1)); printf 'FAIL: %s\n' "$3"
    # Preserve complete diagnostics when the concise first line is insufficient.
    for log in "$WORK/$base.gate.err" "$WORK/$base.skjs.err" \
               "$WORK/$base.check.out" "$WORK/$base.run.out"; do
      if [ -s "$log" ]; then cat "$log"; fi
    done
  fi
}

if [ "$SUITE" = programs ] || [ "$SUITE" = all ]; then
echo "Checking TypeScript programs..."
for f in $(find verification/tests/programs -name '*.ts' | sort); do
  [ -n "$FILTER" ] && case "$f" in *"$FILTER"*) ;; *) continue ;; esac
  kind="$(basename "$(dirname "$f")")"
  base="$(echo "$f" | tr / _)"
  ast="$WORK/$base.ast.json"
  claims="$WORK/$base.claims.json"
  printf '  %s ... ' "${f#verification/tests/}"

  # Stage 1: the trusted front end, which is also the syntactic gate.
  if ! node verification/tools/parse-source.js "$f" > "$ast" 2> "$WORK/$base.gate.err"; then
    if [ "$kind" = "outside" ]; then
      report OK "$f" "gate rejected: $(head -1 "$WORK/$base.gate.err")"
    else
      report FAIL "$f" "gate rejected a program inside the fragment: $(head -1 "$WORK/$base.gate.err")"
    fi
    continue
  fi
  if [ "$kind" = "outside" ]; then
    report FAIL "$f" "the gate accepted a program that is outside the fragment"
    continue
  fi

  # Stage 2: SKJS, untrusted.
  skjs_check "$f" > "$claims" 2> "$WORK/$base.skjs.err"
  skjs_status=$?
  if [ "$kind" = "reject" ]; then
    if [ "$skjs_status" -ne 0 ] && grep -q 'error:' "$WORK/$base.skjs.err"; then
      report OK "$f" "skjs rejected: $(grep -m1 error: "$WORK/$base.skjs.err" | cut -c1-60)"
    elif [ "$skjs_status" -ne 0 ]; then
      report FAIL "$f" "SKJS failed without a type diagnostic (exit $skjs_status)"
    else
      report FAIL "$f" "skjs accepted a program it must reject"
    fi
    continue
  fi
  if [ "$skjs_status" -ne 0 ]; then
    report FAIL "$f" "skjs rejected: $(grep -m1 error: "$WORK/$base.skjs.err" | cut -c1-60)"
    continue
  fi

  # Stage 3: the trusted verifier.
  checked=0
  if "$VERIFIER" "$ast" "$claims" "$f" > "$WORK/$base.check.out" 2>&1; then
    checked=1
  fi

  # Stage 4: agreement with Node. An accepted program must run within its
  # declared types; a known-unsound one must be caught doing otherwise.
  runtime_ok=0
  if node verification/tools/runtime-check.js "$f" "$ast" > "$WORK/$base.run.out" 2>&1; then
    runtime_ok=1
  fi

  detail="$(head -1 "$WORK/$base.check.out" | cut -c1-88)"
  runline="$(head -1 "$WORK/$base.run.out" | cut -c1-88)"
  if [ "$kind" = "known-unsound" ]; then
    # A verdict alone is not evidence: a decoder bug or an arity mismatch would
    # also reject. Where the program carries an `expect-reject:` line, require
    # the checker to have rejected it through that obligation.
    want="$(sed -n 's|^// expect-reject: *||p' "$f" | head -1)"
    if [ "$checked" -eq 1 ]; then
      report FAIL "$f" "the claims checked, but this program is unsound"
    elif [ "$runtime_ok" -eq 1 ]; then
      report FAIL "$f" "the claims were rejected but Node found no violation"
    elif [ -n "$want" ] && ! grep -qF "$want" "$WORK/$base.check.out"; then
      report FAIL "$f" "rejected for the wrong reason: wanted \"$want\", got: $detail"
    else
      report OK "$f" "rejected, and Node agrees: ${runline#violation: }"
    fi
  else
    if [ "$checked" -eq 0 ]; then
      report FAIL "$f" "$detail"
    elif [ "$runtime_ok" -eq 0 ]; then
      report FAIL "$f" "claims checked but Node disagreed: $runline"
    else
      report OK "$f" "claims checked; $runline"
    fi
  fi
done

if [ "$((pass + fail))" -eq 0 ]; then
  echo "FAIL: no programs matched '$FILTER'"
  exit 1
fi
echo "Programs: $pass passed, $fail failed"
fi

# Receiver tests: alter claims and source identifiers in a real claim set.
if [ "$SUITE" = claims ] || [ "$SUITE" = all ]; then
  echo "Testing verifier claim validation..."
  BASE="verification/tests/programs/accept/typeof_narrow.ts"
  OTHER="verification/tests/programs/accept/early_return.ts"
  if ! { node verification/tools/parse-source.js "$BASE" > "$WORK/claims.ast" &&
         node verification/tools/parse-source.js "$OTHER" > "$WORK/claims.other.ast" &&
         skjs_check "$BASE" > "$WORK/claims.claims"; } 2> "$WORK/claims.setup.err"; then
    echo "FAIL: claim validation test setup"
    cat "$WORK/claims.setup.err"
    exit 1
  fi
  if node verification/tests/type-claims.js "$WORK/claims.ast" "$WORK/claims.claims" \
       "$BASE" "$VERIFIER" "$WORK/claims.other.ast" > "$WORK/claims.out" 2>&1; then
    cat "$WORK/claims.out"
  else
    echo "FAIL: claim validation checks"
    cat "$WORK/claims.out"
    fail=$((fail + 1))
  fi
fi

if [ "$SUITE" = stateful-source ] || [ "$SUITE" = all ]; then
  BASE="verification/tests/stateful-source/basic.ts"
  if ! { node verification/tools/parse-source.js "$BASE" > "$WORK/source.ast" &&
         skjs_check "$BASE" > "$WORK/source.claims"; } 2> "$WORK/source.setup.err"; then
    echo "FAIL: stateful source test setup"
    cat "$WORK/source.setup.err"
    exit 1
  fi
  if ! node verification/tests/stateful-source.js "$WORK/source.ast" "$WORK/source.claims" \
       "$BASE" "$VERIFIER"; then
    fail=$((fail + 1))
  fi
  CELL_SOURCE="verification/tests/stateful-source/cells.ts"
  if ! { node verification/tools/parse-source.js "$CELL_SOURCE" --stateful > "$WORK/cells.ast" &&
         skjs_check "$CELL_SOURCE" > "$WORK/cells.claims"; } 2> "$WORK/cells.setup.err"; then
    echo "FAIL: cell source test setup"
    cat "$WORK/cells.setup.err"
    exit 1
  fi
  if ! node verification/tests/stateful-cells.js "$WORK/cells.ast" "$WORK/cells.claims" \
       "$CELL_SOURCE" "$VERIFIER"; then
    fail=$((fail + 1))
  fi
  CLOSURES="verification/tests/stateful-source/closures.ts"
  if ! { node verification/tools/parse-source.js "$CLOSURES" --stateful > "$WORK/closures.ast" &&
         skjs_check "$CLOSURES" > "$WORK/closures.claims"; } 2> "$WORK/closures.setup.err"; then
    echo "FAIL: closure source test setup"
    cat "$WORK/closures.setup.err"
    exit 1
  fi
  if ! node verification/tests/stateful-closures.js "$WORK/closures.ast" "$WORK/closures.claims" \
       "$CLOSURES" "$VERIFIER"; then
    fail=$((fail + 1))
  fi
  LOOPS="verification/tests/stateful-source/loops.ts"
  if ! { node verification/tools/parse-source.js "$LOOPS" --stateful > "$WORK/loops.ast" &&
         skjs_check "$LOOPS" > "$WORK/loops.claims"; } 2> "$WORK/loops.setup.err"; then
    echo "FAIL: loop source test setup"; cat "$WORK/loops.setup.err"; exit 1
  fi
  if ! node verification/tests/stateful-loops.js "$WORK/loops.ast" "$WORK/loops.claims" "$LOOPS" "$VERIFIER"; then exit 1; fi
  if ! node verification/tests/source-claims.js "$VERIFIER"; then exit 1; fi
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
  if ! node verification/tests/source-claim-export.js "$WORK/closures.claims" "$CLOSURES" "$WORK/partial.claims" "$PARTIAL" "$WORK/recovery.claims" "$VERIFIER" "$WORK/partial.err"; then exit 1; fi
  if ! node verification/tests/partial-claims.js "$WORK/partial.claims" "$WORK/recovery.claims" "$PARTIAL" "$VERIFIER" "$WORK/partial.err"; then
    exit 1
  fi
  if ! node verification/tests/annotated-source.js "$WORK/closures.claims" "$CLOSURES" "$VERIFIER"; then
    fail=$((fail + 1))
  fi
  CELLS="verification/tests/stateful-source/cell-contracts.ts"
  if ! skjs_check "$CELLS" > "$WORK/cell.claims" 2> "$WORK/cell.setup.err"; then
    echo "FAIL: cell contract export setup"
    cat "$WORK/cell.setup.err"
    exit 1
  fi
  if ! "$REPO/verification/lean/.lake/build/bin/cell_claim_tests" "$WORK/cell.claims" "$CELLS"; then
    fail=$((fail + 1))
  fi

fi

[ "$fail" -eq 0 ]
