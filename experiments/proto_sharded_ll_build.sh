#!/bin/bash
set -euo pipefail

# Prototype only: splits a monolithic LLVM IR .ll into function shards, compiles
# them in parallel, and links with --allow-multiple-definition because non-function
# definitions are duplicated across shards.
#
# This is an experiment to measure final-stage speed, not a production-safe build.

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
LL_FILE="${1:-$REPO_DIR/target/fast_build/skjs.ll}"
SHARDS="${SHARDS:-8}"
OUT_DIR="${OUT_DIR:-$REPO_DIR/target/fast_build/sharded_proto}"
OUT_BIN="${OUT_BIN:-$OUT_DIR/skjs_sharded_proto}"
DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"

mkdir -p "$OUT_DIR"
rm -rf "$OUT_DIR/shards" "$OUT_DIR/objs"
mkdir -p "$OUT_DIR/shards" "$OUT_DIR/objs"

python3 "$REPO_DIR/experiments/split_llvm_ir_functions.py" "$LL_FILE" --out-dir "$OUT_DIR/shards" --shards "$SHARDS"

docker run --rm -v "$REPO_DIR:/work/skjs" -w /work/skjs "$DOCKER_IMAGE" /bin/sh -lc '
set -e
OUT_DIR="target/fast_build/sharded_proto"
RUNTIME=$(find target/host/dev/build -name libskjs_runtime.a | head -1)
STD=$(find target/host/dev/deps -name "libstd-*.sklib" | head -1)
if [ -z "$RUNTIME" ] || [ -z "$STD" ]; then
  echo "missing runtime/std artifacts; run a normal build first" >&2
  exit 1
fi
c0=$(date +%s%3N)
for f in "$OUT_DIR"/shards/shard_*.ll; do
  b=$(basename "$f" .ll)
  clang++ -O0 -c "$f" -o "$OUT_DIR/objs/$b.o" >"$OUT_DIR/objs/$b.log" 2>&1 &
done
wait
c1=$(date +%s%3N)
echo "[proto-shard] parallel shard compile: $((c1-c0))ms"
l0=$(date +%s%3N)
clang++ -O0 -no-pie -Wl,--gc-sections -Wl,--allow-multiple-definition \
  -o "$OUT_DIR/skjs_sharded_proto" "$OUT_DIR"/objs/shard_*.o "$RUNTIME" "$STD" -lpthread \
  >"$OUT_DIR/link.log" 2>&1
l1=$(date +%s%3N)
echo "[proto-shard] link: $((l1-l0))ms"
echo "[proto-shard] total final-stage prototype: $((l1-c0))ms"
ls -lh "$OUT_DIR/skjs_sharded_proto"
'
