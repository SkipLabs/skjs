#!/bin/bash
# End-to-end tests for the --stdin overlay mode.
set -euo pipefail

SKJS="${SKJS:-./target/host/dev/skjs}"
STUBS="${STUBS:-./import-stubs}"
SKJS_ABS="$(realpath "$SKJS")"
STUBS_ABS="$(realpath "$STUBS")"
TMPDIR="$(mktemp -d)"

trap 'rm -rf "$TMPDIR"' EXIT

successes=0
failures=0

OK=$'\033[32m[OK]\033[0m'
FAIL=$'\033[31m[FAIL]\033[0m'

# Run skjs from $TMPDIR so relative marker paths resolve there.
run_stdin() {
  set +e
  (cd "$TMPDIR" && "$SKJS_ABS" check --stdin --import-stubs "$STUBS_ABS" 2>&1)
  set -e
}

# Run skjs from a specific directory.
run_stdin_in() {
  set +e
  (cd "$1" && "$SKJS_ABS" check --stdin --import-stubs "$STUBS_ABS" 2>&1)
  set -e
}

expect_contains() {
  local test_name="$1"
  local needle="$2"
  local actual="$3"
  if echo "$actual" | grep -qF -- "$needle"; then
    echo "$OK Stdin $test_name"
    successes=$((successes + 1))
  else
    echo "$FAIL Stdin $test_name"
    echo "  expected to contain: $needle"
    echo "  actual:              $actual"
    failures=$((failures + 1))
  fi
}

expect_not_contains() {
  local test_name="$1"
  local needle="$2"
  local actual="$3"
  if echo "$actual" | grep -qF -- "$needle"; then
    echo "$FAIL Stdin $test_name"
    echo "  expected NOT to contain: $needle"
    echo "  actual:                  $actual"
    failures=$((failures + 1))
  else
    echo "$OK Stdin $test_name"
    successes=$((successes + 1))
  fi
}

########################################################################
# Single file
########################################################################
out=$(printf '//// a.ts\nconst x: number = "bad";\n' | run_stdin)
expect_contains "singleFileTypeError" \
  "Type 'bad'" "$out"
expect_contains "singleFilePathInError" \
  "$TMPDIR/a.ts" "$out"

########################################################################
# Multi-file with cross-file import
########################################################################
out=$(
  printf '//// a.ts\nexport const x: number = 1;\n//// b.ts\nimport { x } from "./a.js";\nconst y: string = x;\n' \
    | run_stdin
)
expect_contains "multiFileImportTypeError" \
  "is not compatible with type string" "$out"
expect_contains "multiFileErrorPath" \
  "$TMPDIR/b.ts" "$out"

########################################################################
# Stdin overlays a real disk file
########################################################################
SHADOW_DIR="$TMPDIR/shadowed"
mkdir -p "$SHADOW_DIR"
cat > "$SHADOW_DIR/disk.ts" <<'EOF'
export const v: number = 1;
EOF
out=$(
  printf '//// shadowed/disk.ts\nexport const v: number = "stdin-wins";\n' \
    | run_stdin
)
expect_contains "overlayShadowsDisk" \
  "Type 'stdin-wins'" "$out"

########################################################################
# Negative: non-comment line before first marker
########################################################################
out=$(printf 'const stray = 1;\n//// a.ts\nconst x = 1;\n' | run_stdin)
expect_contains "preambleRejected" \
  "before first '////' marker" "$out"

########################################################################
# Negative: duplicate path
########################################################################
out=$(printf '//// a.ts\nx\n//// a.ts\ny\n' | run_stdin)
expect_contains "duplicatePathRejected" \
  "duplicate path" "$out"

########################################################################
# tsconfig.json from stdin: only .ts files become sources, the
# tsconfig is picked up via the Fs seam during discovery.
########################################################################
TSPROJ="$TMPDIR/tsproj"
mkdir -p "$TSPROJ"
out=$(
  printf '//// %s/tsconfig.json\n{ "compilerOptions": { "strict": true } }\n//// %s/a.ts\nconst x: number = "tsproj-bad";\n' \
    "$TSPROJ" "$TSPROJ" \
    | run_stdin_in "$TSPROJ"
)
expect_contains "tsconfigOverlay" \
  "Type 'tsproj-bad'" "$out"

########################################################################
# Preamble with only comments and blank lines is accepted
########################################################################
out=$(
  printf '\n// banner\n\n//// a.ts\nconst x: number = 1;\n' | run_stdin
)
expect_not_contains "preambleAccepted" \
  "before first '////' marker" "$out"

########################################################################
# Summary
########################################################################
total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
