#!/usr/bin/env bash
#
# Convenience wrapper to run the generated examples checker inside the official
# Skip Docker image, per AGENTS.md.
#
# Usage (from repo root):
#   ./scripts/run-check-generated-examples-docker.sh
#   ONLY_PROJECT=generated-examples/chat-room-service ./scripts/run-check-generated-examples-docker.sh
#
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

if [[ ! -d "${repo_root}/../skip" ]]; then
  echo "ERROR: expected Skip repo at ${repo_root}/../skip"
  echo "Please clone https://github.com/SkipLabs/skip next to this repo."
  exit 2
fi

docker_env_flags=()
for var in ONLY_PROJECT TS_VERSION OUT_DIR CLEAN; do
  if [[ -n "${!var:-}" ]]; then
    docker_env_flags+=(-e "${var}=${!var}")
  fi
done

docker run --rm \
  "${docker_env_flags[@]+"${docker_env_flags[@]}"}" \
  -v "${repo_root}:/work/skjs" \
  -v "${repo_root}/../skip:/work/skip" \
  -w /work/skjs \
  skiplabs/skip:latest \
  bash -lc "./scripts/check-generated-examples.sh"


