#!/bin/bash
# Test suite for incremental type-checking.
# Verifies that only the expected definitions are recomputed when files change.
# Uses __SKJS_show() as a side-effect marker: its output on stderr tells us
# which definitions were (re-)checked.
set -euo pipefail

SKJS="${SKJS:-./target/host/dev/skjs}"
TMPDIR="$(mktemp -d)"
CACHE="$TMPDIR/cache"
FILE="$TMPDIR/test.ts"
STUBS="./import-stubs"

trap 'rm -rf "$TMPDIR"' EXIT

successes=0
failures=0

OK=$'\033[32m[OK]\033[0m'
FAIL=$'\033[31m[FAIL]\033[0m'

# Run skjs check and capture stderr (the __SKJS_show output).
# Usage: run_check [--init|--data] [files...]
# If no files given, defaults to $FILE.
run_check() {
  local mode="$1"; shift
  local files=("$@")
  if [ ${#files[@]} -eq 0 ]; then
    files=("$FILE")
  fi
  "$SKJS" check "$mode" "$CACHE" --import-stubs "$STUBS" "${files[@]}" 2>&1 || true
}

# Assert that the markers on stderr match exactly the expected set.
# Sorts both expected and actual before comparing, since output order
# may vary across files.
expect_markers() {
  local test_name="$1"
  local expected="$2"
  local actual="$3"
  local expected_sorted actual_sorted
  expected_sorted=$(echo "$expected" | sort)
  actual_sorted=$(echo "$actual" | sort)
  if [ "$expected_sorted" = "$actual_sorted" ]; then
    echo "$OK Incremental $test_name"
    successes=$((successes + 1))
  else
    echo "$FAIL Incremental $test_name"
    echo "  expected: $(echo "$expected_sorted" | tr '\n' ' ')"
    echo "  actual:   $(echo "$actual_sorted" | tr '\n' ' ')"
    failures=$((failures + 1))
  fi
}

# Reset cache for a fresh test group.
reset_cache() {
  rm -rf "$CACHE"
}

########################################################################
# Test group: basic functions (single file)
########################################################################

reset_cache
cat > "$FILE" <<'EOF'
function f1(): void {
  __SKJS_show("f1");
}
function f2(): void {
  __SKJS_show("f2");
}
function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --init)
expect_markers "initComputesAllFunctions" "'f1'
'f2'
'f3'" "$out"

out=$(run_check --data)
expect_markers "noChangeNotRecomputed" "" "$out"

########################################################################
# Whitespace-only change → nothing recomputed
########################################################################
cat > "$FILE" <<'EOF'
function f1(): void {
  __SKJS_show("f1");
}

function f2(): void {
  __SKJS_show("f2");
}

function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --data)
expect_markers "whitespaceChangeNotRecomputed" "" "$out"

########################################################################
# Comment-only change → nothing recomputed
########################################################################
cat > "$FILE" <<'EOF'
// This is a comment
function f1(): void {
  __SKJS_show("f1");
}

/* Another comment */
function f2(): void {
  __SKJS_show("f2");
}

function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --data)
expect_markers "commentChangeNotRecomputed" "" "$out"

########################################################################
# Change f2 body → only f2 recomputed
########################################################################
cat > "$FILE" <<'EOF'
// This is a comment
function f1(): void {
  __SKJS_show("f1");
}

/* Another comment */
function f2(): void {
  __SKJS_show("f2");
  let x: number = 42;
}

function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --data)
expect_markers "bodyChangeRecomputesOnlyThatFunction" "'f2'" "$out"

########################################################################
# Change f1 body → only f1 recomputed
########################################################################
cat > "$FILE" <<'EOF'
// This is a comment
function f1(): void {
  __SKJS_show("f1");
  let y: string = "hello";
}

/* Another comment */
function f2(): void {
  __SKJS_show("f2");
  let x: number = 42;
}

function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --data)
expect_markers "anotherBodyChangeRecomputesOnlyThatFunction" "'f1'" "$out"

########################################################################
# Class method body change → class recomputed
########################################################################

reset_cache
cat > "$FILE" <<'EOF'
class C1 {
  m1(): void {
    __SKJS_show("C1.m1");
  }
  m2(): void {
    __SKJS_show("C1.m2");
  }
}
function f1(): void {
  __SKJS_show("f1");
}
EOF

out=$(run_check --init)
expect_markers "initClassAndFunction" "'C1.m1'
'C1.m2'
'f1'" "$out"

out=$(run_check --data)
expect_markers "classNoChangeNotRecomputed" "" "$out"

# Change m1 body
cat > "$FILE" <<'EOF'
class C1 {
  m1(): void {
    __SKJS_show("C1.m1");
    let x: number = 1;
  }
  m2(): void {
    __SKJS_show("C1.m2");
  }
}
function f1(): void {
  __SKJS_show("f1");
}
EOF

out=$(run_check --data)
expect_markers "methodBodyChangeRecomputesClass" "'C1.m1'
'C1.m2'" "$out"

########################################################################
# Signature change propagates to dependents
########################################################################

reset_cache
cat > "$FILE" <<'EOF'
function f1(): number {
  __SKJS_show("f1");
  return 1;
}
function f2(): void {
  __SKJS_show("f2");
  let _x = f1();
}
function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --init)
expect_markers "initWithDependentFunctions" "'f1'
'f2'
'f3'" "$out"

# Change f1's return type (signature change)
cat > "$FILE" <<'EOF'
function f1(): string {
  __SKJS_show("f1");
  return "hello";
}
function f2(): void {
  __SKJS_show("f2");
  let _x = f1();
}
function f3(): void {
  __SKJS_show("f3");
}
EOF

out=$(run_check --data)
expect_markers "signatureChangeRecomputesDependents" "'f1'
'f2'" "$out"

########################################################################
# Two independent classes
########################################################################

reset_cache
cat > "$FILE" <<'EOF'
class A {
  foo(): void {
    __SKJS_show("A.foo");
  }
}
class B {
  bar(): void {
    __SKJS_show("B.bar");
  }
}
EOF

out=$(run_check --init)
expect_markers "initTwoClasses" "'A.foo'
'B.bar'" "$out"

# Change only B
cat > "$FILE" <<'EOF'
class A {
  foo(): void {
    __SKJS_show("A.foo");
  }
}
class B {
  bar(): void {
    __SKJS_show("B.bar");
    let z: number = 0;
  }
}
EOF

out=$(run_check --data)
expect_markers "independentClassChangeRecomputesOnlyThatClass" "'B.bar'" "$out"

########################################################################
# Multi-file: function body change
########################################################################

FOO="$TMPDIR/foo.ts"
BAR="$TMPDIR/bar.ts"

reset_cache
cat > "$FOO" <<'EOF'
export function helper(): number {
  __SKJS_show("helper");
  return 42;
}
EOF
cat > "$BAR" <<'EOF'
import { helper } from "./foo.js";
function user(): void {
  __SKJS_show("user");
  let _x = helper();
}
function independent(): void {
  __SKJS_show("independent");
}
EOF

out=$(run_check --init "$FOO" "$BAR")
expect_markers "multiFileInit" "'helper'
'user'
'independent'" "$out"

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileNoChangeNotRecomputed" "" "$out"

# Change helper body only (return value, same type)
cat > "$FOO" <<'EOF'
export function helper(): number {
  __SKJS_show("helper");
  return 100;
}
EOF

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileBodyChangeDoesNotPropagate" "'helper'" "$out"

########################################################################
# Multi-file: signature change propagates across files
########################################################################

# Change helper's return type
cat > "$FOO" <<'EOF'
export function helper(): string {
  __SKJS_show("helper");
  return "hello";
}
EOF

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileSignatureChangePropagates" "'helper'
'user'" "$out"

########################################################################
# Multi-file: class body vs signature
########################################################################

reset_cache
cat > "$FOO" <<'EOF'
export class Foo {
  getValue(): number {
    __SKJS_show("Foo.getValue");
    return 42;
  }
  getName(): string {
    __SKJS_show("Foo.getName");
    return "foo";
  }
}
EOF
cat > "$BAR" <<'EOF'
import { Foo } from "./foo.js";
function useFoo(): void {
  __SKJS_show("useFoo");
  let f = new Foo();
  let _v = f.getValue();
}
function independent(): void {
  __SKJS_show("independent");
}
EOF

out=$(run_check --init "$FOO" "$BAR")
expect_markers "multiFileClassInit" "'Foo.getValue'
'Foo.getName'
'useFoo'
'independent'" "$out"

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileClassNoChangeNotRecomputed" "" "$out"

# Change a method body in Foo
cat > "$FOO" <<'EOF'
export class Foo {
  getValue(): number {
    __SKJS_show("Foo.getValue");
    return 100;
  }
  getName(): string {
    __SKJS_show("Foo.getName");
    return "foo";
  }
}
EOF

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileClassBodyChangePropagates" "'Foo.getValue'
'Foo.getName'
'useFoo'" "$out"

########################################################################
# Multi-file: consumer change doesn't affect provider
########################################################################

# Change useFoo body in bar.ts
cat > "$BAR" <<'EOF'
import { Foo } from "./foo.js";
function useFoo(): void {
  __SKJS_show("useFoo");
  let f = new Foo();
  let _v = f.getValue();
  let _n = f.getName();
}
function independent(): void {
  __SKJS_show("independent");
}
EOF

out=$(run_check --data "$FOO" "$BAR")
expect_markers "multiFileConsumerChangeDoesNotAffectProvider" "'useFoo'" "$out"

########################################################################
# Multi-file: shared dependency (3 files)
########################################################################

TYPES="$TMPDIR/types.ts"
A="$TMPDIR/a.ts"
B="$TMPDIR/b.ts"

reset_cache
cat > "$TYPES" <<'EOF'
export function getNum(): number {
  __SKJS_show("getNum");
  return 1;
}
EOF
cat > "$A" <<'EOF'
import { getNum } from "./types.js";
function useNum(): void {
  __SKJS_show("useNum");
  let _x = getNum();
}
EOF
cat > "$B" <<'EOF'
import { getNum } from "./types.js";
function useNum2(): void {
  __SKJS_show("useNum2");
  let _y = getNum();
}
function standalone(): void {
  __SKJS_show("standalone");
}
EOF

out=$(run_check --init "$TYPES" "$A" "$B")
expect_markers "multiFileSharedDepInit" "'getNum'
'useNum'
'useNum2'
'standalone'" "$out"

out=$(run_check --data "$TYPES" "$A" "$B")
expect_markers "multiFileSharedDepNoChangeNotRecomputed" "" "$out"

# Change shared dep body
cat > "$TYPES" <<'EOF'
export function getNum(): number {
  __SKJS_show("getNum");
  return 999;
}
EOF

out=$(run_check --data "$TYPES" "$A" "$B")
expect_markers "multiFileSharedDepBodyChangeDoesNotPropagate" "'getNum'" "$out"

# Change shared dep signature
cat > "$TYPES" <<'EOF'
export function getNum(): string {
  __SKJS_show("getNum");
  return "hi";
}
EOF

out=$(run_check --data "$TYPES" "$A" "$B")
expect_markers "multiFileSharedDepSignatureChangePropagates" "'getNum'
'useNum'
'useNum2'" "$out"

########################################################################
# Summary
########################################################################
total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
