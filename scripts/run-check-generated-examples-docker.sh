#!/usr/bin/env bash
#
# Convenience wrapper to run the generated examples checker inside the official
# Skip Docker image, per AGENTS.md.
#
# Usage (from repo root):
#   ./scripts/run-check-generated-examples-docker.sh [--clean]
#
# Forwards optional environment variables (TS_VERSION, OUT_DIR, CLEAN,
# ONLY_PROJECT, SKJS_PROFILE, SKJS_BIN, BASELINE_TSV, MAX_REGRESSION_PCT,
# MIN_REGRESSION_MS) into the container.
#
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
skip_dir="${SKIP_DIR:-${repo_root}/../skip}"

if [[ ! -d "${skip_dir}" ]]; then
  echo "ERROR: expected Skip repo at ${skip_dir} (override with SKIP_DIR)"
  echo "Please clone https://github.com/SkipLabs/skip next to this repo."
  exit 2
fi

env_args=()
for var in TS_VERSION OUT_DIR CLEAN ONLY_PROJECT SKJS_PROFILE SKJS_BIN \
           BASELINE_TSV MAX_REGRESSION_PCT MIN_REGRESSION_MS; do
  if [[ -n "${!var:-}" ]]; then
    env_args+=(-e "${var}=${!var}")
  fi
done

docker run --rm \
  "${env_args[@]}" \
  -v "${repo_root}:/work/skjs" \
  -v "${skip_dir}:/work/skip" \
  -w /work/skjs \
  skiplabs/skip:latest \
  ./scripts/check-generated-examples.sh "$@"


