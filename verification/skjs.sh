#!/usr/bin/env bash
# Shared SKJS invocation for pipeline regressions and example reports.
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SKJS_BIN="${SKJS_BIN:-target/host/dev/skjs}"
DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"
SKIP_DIR="${SKIP_DIR:-$REPO/../skip}"
cd "$REPO" || exit 1

# Starting a container costs more than checking a source, so a caller that makes
# many checks starts one and runs them all inside it. The name is exported
# before any work forks, so callers that check in parallel share the container
# rather than each starting one. Nothing is required to call this: without it
# every check starts its own, which is what a single one-shot check wants.
skjs_start() {
  [ -n "${DEVCONTAINER:-}" ] && return 0
  [ -n "${SKJS_CONTAINER:-}" ] && return 0
  SKJS_CONTAINER="$(docker run -d --rm -v "$REPO:/work/skjs" -v "$SKIP_DIR:/work/skip" \
    -w /work/skjs "$DOCKER_IMAGE" sleep 900)" || return 1
  # The name crosses into child processes; the ownership does not, so a run that
  # was handed a container leaves it for whoever started it.
  export SKJS_CONTAINER
  SKJS_CONTAINER_OWNER=$$
}

# The container holds no state a later run should inherit, and it stops itself
# after the sleep even if this is missed.
skjs_shutdown() {
  [ -n "${SKJS_CONTAINER:-}" ] || return 0
  [ "${SKJS_CONTAINER_OWNER:-}" = "$$" ] || return 0
  docker rm -f "$SKJS_CONTAINER" > /dev/null 2>&1
  unset SKJS_CONTAINER SKJS_CONTAINER_OWNER
}

skjs_run() { # CLI options, then repo-relative source paths
  if [ -n "${DEVCONTAINER:-}" ]; then
    "$SKJS_BIN" check --import-stubs import-stubs --truthiness boolean \
      "$@"
  elif [ -n "${SKJS_CONTAINER:-}" ]; then
    docker exec "$SKJS_CONTAINER" \
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
