#!/bin/bash
# Test suite for config changes against a persistent cache.
# The effective checker config is a tracked SKStore input (src/Config.sk):
# a --data run with different CLI/tsconfig options must recompute affected
# results instead of serving ones cached under the old config.
set -euo pipefail

SKJS="${SKJS:-./target/host/dev/skjs}"
TMPDIR="$(mktemp -d)"
CACHE="$TMPDIR/cache"
STUBS="./import-stubs"

trap 'rm -rf "$TMPDIR"' EXIT

successes=0
failures=0

OK=$'\033[32m[OK]\033[0m'
FAIL=$'\033[31m[FAIL]\033[0m'

# Run a check and capture stderr (diagnostics). Never fails the script:
# type errors are expected output here.
# Usage: run_check <extra-args...>
run_check() {
  {
    "$SKJS" check --keep-going --import-stubs "$STUBS" "$@" \
      "$TMPDIR/cond.ts" >/dev/null
  } 2>&1 || true
}

# Assert that diagnostics contain a string.
# Usage: expect_contains <test_name> <needle> <output>
expect_contains() {
  local test_name="$1"
  local needle="$2"
  local output="$3"
  if echo "$output" | grep -qF "$needle"; then
    echo "$OK ConfigChange $test_name"
    successes=$((successes + 1))
  else
    echo "$FAIL ConfigChange $test_name"
    echo "  expected diagnostics to contain: $needle"
    echo "  got:"
    echo "    ${output//$'\n'/$'\n'    }"
    failures=$((failures + 1))
  fi
}

# A number condition: diagnosed differently by truthiness modes.
# Default ("safe"): "A condition is expected to be of type boolean or a type
# with a single falsy value". Boolean mode: "A condition must be of type
# 'boolean'".
cat > "$TMPDIR/cond.ts" <<'EOF'
function f(n: number): string {
  if (n) {
    return "y";
  }
  return "n";
}
EOF

SAFE_MSG="A condition is expected to be of type boolean"
BOOL_MSG="A condition must be of type 'boolean'"

# Prime the cache under the default truthiness mode.
out=$(run_check --init "$CACHE")
expect_contains "initDefaultTruthiness" "$SAFE_MSG" "$out"

# A --data run with a different truthiness must recompute under the new
# mode, not serve the cached safe-mode diagnostic.
out=$(run_check --data "$CACHE" --truthiness=boolean)
expect_contains "dataRunSeesNewTruthiness" "$BOOL_MSG" "$out"

# And switching back must restore the original diagnostic.
out=$(run_check --data "$CACHE")
expect_contains "dataRunSeesRestoredTruthiness" "$SAFE_MSG" "$out"

total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
