#!/usr/bin/env bash
# Performance regression test for incremental type-checking (issue #1034).
#
# Primes a persistent SKStore cache on a multi-file fixture, then measures
# incremental `--data` runs for:
#   1. warm no-op re-check
#   2. single function-body edit (should stay on the fast path)
#   3. leading comment inserted above a shared types.ts (must not trigger a
#      full re-check of dependent files; regression guard for #1031)
#
# Fails if any incremental run exceeds a generous wall-clock budget (default
# 2000 ms, overridable via SKJS_PERF_BUDGET_MS) so a regression that turns the
# ~tens-of-ms incremental path into a multi-second full re-check cannot pass
# `make test` unnoticed.
#
# Environment:
#   SKJS                  path to skjs binary (default: release if present,
#                         else ./target/host/dev/skjs)
#   SKJS_PERF_BUDGET_MS   max allowed latency in ms for each incremental check
#                         (default: 2000)
#   SKJS_PERF_MODULES     number of synthetic consumer modules (default: 20)
set -euo pipefail

if [ -n "${SKJS:-}" ]; then
  SKJS_BIN="$SKJS"
elif [ -x "./target/host/release/skjs" ]; then
  SKJS_BIN="./target/host/release/skjs"
else
  SKJS_BIN="./target/host/dev/skjs"
fi

BUDGET_MS="${SKJS_PERF_BUDGET_MS:-2000}"
NUM_MODULES="${SKJS_PERF_MODULES:-20}"
STUBS="./import-stubs"
TMPDIR="$(mktemp -d)"
CACHE="$TMPDIR/cache"
SRC="$TMPDIR/src"

trap 'rm -rf "$TMPDIR"' EXIT

if [ ! -x "$SKJS_BIN" ]; then
  echo "ERROR: skjs binary not found or not executable: $SKJS_BIN" >&2
  exit 2
fi

successes=0
failures=0

OK=$'\033[32m[OK]\033[0m'
FAIL=$'\033[31m[FAIL]\033[0m'

# Portable millisecond timestamp (GNU date %s%3N, fallback to node/python3).
now_ms() {
  local ts
  ts="$(date +%s%3N 2>/dev/null || true)"
  if [[ "$ts" =~ ^[0-9]+$ ]]; then
    printf '%s\n' "$ts"
  elif command -v node >/dev/null 2>&1; then
    node -e 'process.stdout.write(String(Date.now()))'
  else
    python3 -c 'import time; print(int(time.time() * 1000))'
  fi
}

# Build a clean multi-file TypeScript fixture with a shared types.ts and
# NUM_MODULES consumer modules importing from it.
mkdir -p "$SRC"
cat > "$SRC/types.ts" <<'EOF'
export type RecordId = string;
export type Status = "active" | "inactive" | "pending";
export type Item = {
  readonly id: RecordId;
  readonly name: string;
  readonly count: number;
  readonly status: Status;
  readonly tags: readonly string[];
};
export type Summary = {
  readonly total: number;
  readonly active: number;
  readonly label: string;
};
EOF

FILES=("$SRC/types.ts")
for i in $(seq 1 "$NUM_MODULES"); do
  mod="$SRC/mod_${i}.ts"
  cat > "$mod" <<EOF
import type { Item, Status, Summary } from "./types.js";

export interface Module${i}Config {
  readonly prefix: string;
  readonly limit: number;
}

export function scoreItem${i}(item: Item, cfg: Module${i}Config): number {
  let base: number = item.count;
  if (item.status === "active") {
    base = base + cfg.limit;
  } else if (item.status === "pending") {
    base = base + 1;
  }
  return base;
}

export function summarize${i}(
  items: readonly Item[],
  cfg: Module${i}Config,
): Summary {
  let total: number = 0;
  let active: number = 0;
  for (let idx = 0; idx < items.length; idx = idx + 1) {
    const it = items[idx];
    if (it !== undefined) {
      total = total + scoreItem${i}(it, cfg);
      if (it.status === "active") {
        active = active + 1;
      }
    }
  }
  return { total, active, label: cfg.prefix };
}

export function formatStatus${i}(s: Status): string {
  switch (s) {
    case "active":
      return "A";
    case "inactive":
      return "I";
    case "pending":
      return "P";
  }
}
EOF
  FILES+=("$mod")
done

# Measure a check run and assert exit code 0 and (when max_ms > 0) latency <= max_ms.
# Usage: check_timed <test_name> <--init|--data> <max_ms>
check_timed() {
  local test_name="$1"
  local mode="$2"
  local max_ms="$3"
  local start_ms end_ms elapsed_ms rc output

  start_ms="$(now_ms)"
  set +e
  output="$("$SKJS_BIN" check "$mode" "$CACHE" --import-stubs "$STUBS" "${FILES[@]}" 2>&1)"
  rc=$?
  set -e
  end_ms="$(now_ms)"
  elapsed_ms=$((end_ms - start_ms))

  if [ "$rc" -ne 0 ]; then
    echo "$FAIL IncrementalPerf $test_name (exit=$rc, ${elapsed_ms}ms)"
    echo "$output" | head -n 20 | sed 's/^/  /'
    failures=$((failures + 1))
    return
  fi

  if [ "$max_ms" -gt 0 ] && [ "$elapsed_ms" -gt "$max_ms" ]; then
    echo "$FAIL IncrementalPerf $test_name (${elapsed_ms}ms > budget ${max_ms}ms)"
    failures=$((failures + 1))
    return
  fi

  if [ "$max_ms" -gt 0 ]; then
    echo "$OK IncrementalPerf $test_name (${elapsed_ms}ms <= ${max_ms}ms)"
  else
    echo "$OK IncrementalPerf $test_name (${elapsed_ms}ms, cold init)"
  fi
  successes=$((successes + 1))
}

# 1. Cold check to prime the cache (not latency-gated; reports baseline time).
check_timed "coldInit" --init 0

# 2. Warm no-op check.
check_timed "warmNoop" --data "$BUDGET_MS"

# 3. Single function-body edit in one consumer module.
sed -i.bak 's/base = base + 1;/base = base + 2;/' "$SRC/mod_1.ts"
rm -f "$SRC/mod_1.ts.bak"
check_timed "singleBodyEdit" --data "$BUDGET_MS"

# 4. Leading comment inserted at top of shared types.ts (shifts line numbers
#    of exported type aliases without changing their meaning).
{
  printf '// leading comment shifting exported type aliases\n'
  cat "$SRC/types.ts"
} > "$SRC/types.ts.new"
mv "$SRC/types.ts.new" "$SRC/types.ts"
check_timed "commentAboveTypesAlias" --data "$BUDGET_MS"

total=$((successes + failures))
echo "Failures: $failures, successes: $successes (total: $total)"
if [ "$failures" -gt 0 ]; then
  exit 1
fi
