#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

LL_FILE="${1:-$SCRIPT_DIR/skjs.ll}"
SHARDS="${SHARDS:-8}"
DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"
OUT_DIR="${OUT_DIR:-$REPO_DIR/target/fast_build/ll_split_demo_measure}"

if [ ! -f "$LL_FILE" ]; then
  echo "missing input .ll file: $LL_FILE" >&2
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -rf "$OUT_DIR"/baseline "$OUT_DIR"/sharded
mkdir -p "$OUT_DIR"/baseline "$OUT_DIR"/sharded/shards "$OUT_DIR"/sharded/objs

now_ms() {
  local ts
  ts=$(date +%s%3N 2>/dev/null || true)
  case "$ts" in
    ''|*[!0-9]*)
      python3 -c 'import time; print(int(time.time()*1000))'
      ;;
    *)
      echo "$ts"
      ;;
  esac
}

echo "[measure] input: $LL_FILE"
echo "[measure] shards: $SHARDS"
echo "[measure] out:   $OUT_DIR"

split_t0=$(now_ms)
python3 "$REPO_DIR/experiments/split_llvm_ir_functions.py" \
  "$LL_FILE" \
  --out-dir "$OUT_DIR/sharded/shards" \
  --shards "$SHARDS"
split_t1=$(now_ms)
split_ms=$((split_t1 - split_t0))
echo "[measure] split: ${split_ms}ms"

docker run --rm \
  -v "$REPO_DIR:/work/skjs" \
  -w /work/skjs \
  -e OUT_DIR_INNER="${OUT_DIR#$REPO_DIR/}" \
  -e LL_FILE_INNER="${LL_FILE#$REPO_DIR/}" \
  -e SHARDS="$SHARDS" \
  "$DOCKER_IMAGE" /bin/sh -lc '
set -e

now_ms() {
  date +%s%3N
}

OUT_DIR="${OUT_DIR_INNER}"
LL_FILE="${LL_FILE_INNER}"
RUNTIME=$(find target/host/dev/build -name libskjs_runtime.a | head -1)
STD=$(find target/host/dev/deps -name "libstd-*.sklib" | head -1)
if [ -z "$RUNTIME" ] || [ -z "$STD" ]; then
  echo "missing runtime/std artifacts; run a normal build first" >&2
  exit 1
fi

b0=$(now_ms)
clang++ -O0 -no-pie -o "$OUT_DIR/baseline/skjs_mono" "$LL_FILE" "$RUNTIME" "$STD" -lpthread \
  >"$OUT_DIR/baseline/clang.log" 2>&1
b1=$(now_ms)
baseline_ms=$((b1-b0))
echo "[measure] baseline_mono_clang: ${baseline_ms}ms"

c0=$(now_ms)
for f in "$OUT_DIR"/sharded/shards/shard_*.ll; do
  b=$(basename "$f" .ll)
  clang++ -O0 -c "$f" -o "$OUT_DIR/sharded/objs/$b.o" >"$OUT_DIR/sharded/objs/$b.log" 2>&1 &
done
wait
c1=$(now_ms)
shard_compile_ms=$((c1-c0))
echo "[measure] sharded_parallel_compile: ${shard_compile_ms}ms"

l0=$(now_ms)
clang++ -O0 -no-pie -Wl,--gc-sections -Wl,--allow-multiple-definition \
  -o "$OUT_DIR/sharded/skjs_sharded" "$OUT_DIR"/sharded/objs/shard_*.o "$RUNTIME" "$STD" -lpthread \
  >"$OUT_DIR/sharded/link.log" 2>&1
l1=$(now_ms)
shard_link_ms=$((l1-l0))
echo "[measure] sharded_link: ${shard_link_ms}ms"

shard_total_ms=$((l1-c0))
echo "[measure] sharded_compile_plus_link: ${shard_total_ms}ms"
'
