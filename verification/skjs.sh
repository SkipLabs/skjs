#!/usr/bin/env bash
# Shared SKJS invocation for pipeline regressions and example reports.
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SKJS_BIN="${SKJS_BIN:-target/host/dev/skjs}"
DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"
SKIP_DIR="${SKIP_DIR:-$REPO/../skip}"
cd "$REPO" || exit 1

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

# One invocation can carry many sources, and the claim array names each file.
# A container start costs more than checking a small file, so batching callers
# should pass every source at once rather than looping.
skjs_check() { skjs_run --emit-skjs-type-claims "$@"; }

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  skjs_run "$@"
fi
