#!/usr/bin/env bash
#
# Convenience wrapper to run the generated examples checker inside the official
# Skip Docker image, per AGENTS.md.
#
# Usage (from repo root):
#   ./scripts/run-check-generated-examples-docker.sh
#
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

if [[ ! -d "${repo_root}/../skip" ]]; then
  echo "ERROR: expected Skip repo at ${repo_root}/../skip"
  echo "Please clone https://github.com/SkipLabs/skip next to this repo."
  exit 2
fi

docker run --rm \
  -v "${repo_root}:/work/skjs" \
  -v "${repo_root}/../skip:/work/skip" \
  -w /work/skjs \
  skiplabs/skip:latest \
  bash -lc "./scripts/check-generated-examples.sh"


