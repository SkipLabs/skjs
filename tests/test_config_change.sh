#!/bin/bash
# Test suite for config changes against a persistent cache.
# The effective checker config is a tracked SKStore input (src/Config.sk):
# a --data run with different CLI/tsconfig options must recompute affected
# results instead of serving ones cached under the old config.
set -euo pipefail

SKJS="${SKJS:-./target/host/dev/skjs}"
SKJS_ABS="$(realpath "$SKJS")"
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
  if echo "$output" | grep -qF -- "$needle"; then
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

# Layered --import-stubs directories (e.g. builtins + project node_modules)
# and missing --import-stubs when node_modules/ exists in the project root.
# Pre-#615 behavior pinned here; updated in the implementation commit.
STUBS_ABS="$(realpath "$STUBS")"
LAYER_DIR="$TMPDIR/layered"
mkdir -p "$LAYER_DIR/node_modules/greet-pkg"
cat > "$LAYER_DIR/node_modules/greet-pkg/index.d.ts" <<'EOF'
export declare function hello(name: string): string;
EOF
cat > "$LAYER_DIR/app.ts" <<'EOF'
import { hello } from "greet-pkg";
function use(): string {
  return hello("world");
}
EOF

layer_out=$("$SKJS" check --import-stubs "$STUBS_ABS" \
  --import-stubs "$LAYER_DIR/node_modules" "$LAYER_DIR/app.ts" 2>&1 || true)
expect_contains "layeredImportStubsWarnsBefore615" \
  "More than one --import-stubs specified; using first one for builtins file" \
  "$layer_out"

missing_nm_out=$(
  cd "$LAYER_DIR" && "$SKJS_ABS" check "$LAYER_DIR/app.ts" 2>&1 || true
)
expect_contains "missingImportStubsRequiresFlag" \
  "--import-stubs is required" "$missing_nm_out"
if echo "$missing_nm_out" | grep -qF -- "--import-stubs ./node_modules"; then
  echo "$FAIL ConfigChange missingImportStubsNoNodeModulesHintBefore615"
  echo "  expected no node_modules hint before #615, got: $missing_nm_out"
  failures=$((failures + 1))
else
  echo "$OK ConfigChange missingImportStubsNoNodeModulesHintBefore615"
  successes=$((successes + 1))
fi

total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
