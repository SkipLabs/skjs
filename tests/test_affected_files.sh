#!/bin/bash
# Test suite for incremental affected-files detection.
# Verifies that --log-affected-files reports the correct set of files
# when definitions change across multiple files.
#
# Uses --keep-going so that the call graph is complete even when
# structural changes introduce type errors.
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

# Run skjs check --init to prime the cache.
# Usage: run_init [files...]
run_init() {
  local files=("$@")
  "$SKJS" check --init "$CACHE" --keep-going --import-stubs "$STUBS" \
    "${files[@]}" >/dev/null 2>&1 || true
}

# Run skjs check --data --log-affected-files and capture stdout (affected
# file paths).  Stderr (type-check markers, diagnostics) is discarded.
# Usage: run_affected [files...]
run_affected() {
  local files=("$@")
  "$SKJS" check --data "$CACHE" --log-affected-files --keep-going \
    --import-stubs "$STUBS" "${files[@]}" 2>/dev/null || true
}

# Compare sorted basenames of affected files against expected set.
# Usage: expect_affected <test_name> <expected_basenames> <actual_output>
# expected_basenames: newline-separated basenames (e.g. "a.ts\nb.ts")
# actual_output: raw stdout from run_affected (absolute paths, one per line)
expect_affected() {
  local test_name="$1"
  local expected="$2"
  local actual="$3"

  # Extract basenames from absolute paths
  local actual_basenames
  if [ -z "$actual" ]; then
    actual_basenames=""
  else
    actual_basenames=$(echo "$actual" | xargs -n1 basename | sort)
  fi

  local expected_sorted
  if [ -z "$expected" ]; then
    expected_sorted=""
  else
    expected_sorted=$(echo "$expected" | sort)
  fi

  if [ "$expected_sorted" = "$actual_basenames" ]; then
    echo "$OK AffectedFiles $test_name"
    successes=$((successes + 1))
  else
    echo "$FAIL AffectedFiles $test_name"
    echo "  expected: $(echo "$expected_sorted" | tr '\n' ' ')"
    echo "  actual:   $(echo "$actual_basenames" | tr '\n' ' ')"
    failures=$((failures + 1))
  fi
}

# Reset cache for a fresh test group.
reset_cache() {
  rm -rf "$CACHE"
}

########################################################################
# Test group 1: Function call chain
# c.ts exports helperC, b.ts imports helperC and exports helperB,
# a.ts imports helperB and exports a, unrelated.ts is standalone.
# Adding an optional parameter to helperC should transitively affect
# a.ts, b.ts, c.ts via the call graph (non-breaking signature change).
########################################################################

C="$TMPDIR/c.ts"
B="$TMPDIR/b.ts"
A="$TMPDIR/a.ts"
UNRELATED="$TMPDIR/unrelated.ts"

reset_cache
cat > "$C" <<'EOF'
export function helperC(): number {
  return 1;
}
EOF
cat > "$B" <<'EOF'
import { helperC } from "./c.js";
export function helperB(): number {
  return helperC();
}
EOF
cat > "$A" <<'EOF'
import { helperB } from "./b.js";
export function a(): number {
  return helperB();
}
EOF
cat > "$UNRELATED" <<'EOF'
export function unrelated(): number {
  return 99;
}
EOF

run_init "$C" "$B" "$A" "$UNRELATED"

# Add optional parameter to helperC (non-breaking signature change)
cat > "$C" <<'EOF'
export function helperC(x?: string): number {
  return 1;
}
EOF

out=$(run_affected "$C" "$B" "$A" "$UNRELATED")
expect_affected "callChainLeafOptionalParam" "a.ts
b.ts
c.ts" "$out"

########################################################################
# Test group 2: Unrelated function change
# Same files, fresh cache.  Changing unrelated's return type should only
# affect unrelated.ts.
########################################################################

reset_cache

cat > "$C" <<'EOF'
export function helperC(): number {
  return 1;
}
EOF
cat > "$B" <<'EOF'
import { helperC } from "./c.js";
export function helperB(): number {
  return helperC();
}
EOF
cat > "$A" <<'EOF'
import { helperB } from "./b.js";
export function a(): number {
  return helperB();
}
EOF
cat > "$UNRELATED" <<'EOF'
export function unrelated(): number {
  return 99;
}
EOF

run_init "$C" "$B" "$A" "$UNRELATED"

# Change unrelated's return type: number -> string
cat > "$UNRELATED" <<'EOF'
export function unrelated(): string {
  return "changed";
}
EOF

out=$(run_affected "$C" "$B" "$A" "$UNRELATED")
expect_affected "unrelatedChange" "unrelated.ts" "$out"

########################################################################
# Test group 3: Class hierarchy
# base.ts exports Base class, child.ts exports Child extends Base,
# user.ts imports Child and calls method(), unrelated2.ts is standalone.
# Adding a new method to Base should transitively affect base.ts,
# child.ts, user.ts via the class hierarchy (non-breaking change).
########################################################################

BASE="$TMPDIR/base.ts"
CHILD="$TMPDIR/child.ts"
USER="$TMPDIR/user.ts"
UNRELATED2="$TMPDIR/unrelated2.ts"

reset_cache

cat > "$BASE" <<'EOF'
export class Base {
  method(): number {
    return 1;
  }
}
EOF
cat > "$CHILD" <<'EOF'
import { Base } from "./base.js";
export class Child extends Base {
  childMethod(): number {
    return 2;
  }
}
EOF
cat > "$USER" <<'EOF'
import { Child } from "./child.js";
export function useChild(): number {
  let c = new Child();
  return c.method();
}
EOF
cat > "$UNRELATED2" <<'EOF'
export function standalone(): number {
  return 42;
}
EOF

run_init "$BASE" "$CHILD" "$USER" "$UNRELATED2"

# Add new method to Base (non-breaking structural change)
cat > "$BASE" <<'EOF'
export class Base {
  method(): number {
    return 1;
  }
  newMethod(): void {}
}
EOF

out=$(run_affected "$BASE" "$CHILD" "$USER" "$UNRELATED2")
expect_affected "classHierarchyNewMethod" "base.ts
child.ts
user.ts" "$out"

########################################################################
# Summary
########################################################################
total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
