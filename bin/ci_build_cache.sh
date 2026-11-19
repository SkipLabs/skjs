#!/bin/bash

# CI cache for the skjs dev binaries (target/host/dev/skjs and
# target/host/dev/test), used by .circleci/config.yml and
# .github/workflows/arm64-test.yml:
#
#   ci_build_cache.sh key       print a fingerprint of the binaries' build
#                               inputs; CI snapshots it and uses it as the
#                               restore_cache/save_cache key
#   ci_build_cache.sh restored  exit 0 when both dev binaries are present
#                               (i.e. the cache was hit), 1 otherwise; CI
#                               uses this to set SKJS_PREBUILT=1 so
#                               `make test` runs the prebuilt test binary
#                               instead of rebuilding via `skargo test`
#
# The fingerprint covers everything `skargo test` compiles: the skjs sources
# and build script, the native runtime sources, and the sources and
# Skargo.toml of skjs's transitive path dependencies (under ../skip, derived
# from the path = "..." entries the same way generate_config.sh derives
# them), plus the toolchain in /usr/bin and /usr/lib and the native compiler
# versions. A change to any of those yields a new key and a full rebuild, so
# a restored binary is always built from the same inputs. The key is computed
# after the Skip repository is cloned, and deliberately does NOT include the
# git HEAD: build.sk embeds GIT_COMMIT_HASH only as --version provenance, and
# skargo's own fingerprints would invalidate a restored target/ on every new
# commit anyway (they hash source mtimes and HEAD), which is why this caches
# the final binaries instead of target/. The save step runs only after the
# tests pass, so a broken binary is never cached. Bump the v1 in the CI
# configs' key prefix only to bust a bad cache.

set -euo pipefail

SKJS_BIN=target/host/dev/skjs
TEST_BIN=target/host/dev/test

# Print skjs and its transitive path dependencies, one per line.
dep_dirs() {
  echo .
  local -a queue=(.)
  local seen=" . "
  local cur dep resolved
  while [ "${#queue[@]}" -gt 0 ]; do
    cur="${queue[0]}"
    queue=("${queue[@]:1}")
    while IFS= read -r dep; do
      [ -n "$dep" ] || continue
      resolved=$(realpath -m --relative-to=. "$cur/$dep" 2>/dev/null) || continue
      [ -f "$resolved/Skargo.toml" ] || continue
      case "$seen" in *" $resolved "*) continue ;; esac
      seen="$seen$resolved "
      echo "$resolved"
      queue+=("$resolved")
    done < <(awk '/^\[(dev-|build-)?dependencies\]/{d=1;next} /^\[/{d=0} d && /path"? *=/{print}' "$cur/Skargo.toml" \
             | grep -oE '"?path"? *= *"[^"]+"' | sed 's/.*"\(.*\)"/\1/')
  done
}

key() {
  local dir f
  {
    for dir in $(dep_dirs); do
      if [ -f "$dir/Skargo.toml" ]; then sha256sum "$dir/Skargo.toml"; fi
      if [ -f "$dir/build.sk" ]; then sha256sum "$dir/build.sk"; fi
      if [ -d "$dir/src" ]; then
        find "$dir/src" -type f -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum
      fi
    done
    # skjs-only build inputs: the native runtime and (for the merged test
    # binary) the test sources.
    sha256sum runtime.cpp runtime.h
    find tests -type f -name '*.sk' -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum
    # The toolchain skc/skargo build and link with.
    for f in /usr/bin/skc /usr/bin/skargo; do
      if [ -f "$f" ]; then sha256sum "$f"; else echo "missing: $f"; fi
    done
    find /usr/lib -maxdepth 1 \( -name '*.sklib' -o -name 'lib*.a' \) -type f -print0 \
      | LC_ALL=C sort -z | xargs -0 -r sha256sum
    # The native compiler and linker skargo invokes for the host binary.
    clang --version 2>/dev/null | head -n 1 || true
    ld.lld --version 2>/dev/null | head -n 1 || true
  } | sha256sum | cut -d' ' -f1
}

restored() {
  if [ -x "$SKJS_BIN" ] && [ -x "$TEST_BIN" ]; then
    echo "restored cached $SKJS_BIN and $TEST_BIN"
    exit 0
  fi
  echo "no cached dev binaries for this key; building from source"
  exit 1
}

case "${1:-}" in
  key) key ;;
  restored) restored ;;
  *)
    echo "usage: $0 key | restored" >&2
    exit 2
    ;;
esac
