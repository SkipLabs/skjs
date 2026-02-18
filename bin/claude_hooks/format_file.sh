#!/bin/bash

# Format a single file based on its extension.
# Called by Claude Code PostToolUse hook with JSON on stdin.

file_path=$(jq -r '.tool_input.file_path // empty')

if [ -z "$file_path" ]; then
    exit 0
fi

# skip files matching *-prettier-ignore.*
if [[ "$file_path" =~ .*-prettier-ignore\..* ]]; then
    exit 0
fi

PRETTIER_VERSION=$(jq -r '.devDependencies.prettier' "$CLAUDE_PROJECT_DIR/package.json")

case "$file_path" in
    *.sk)
        if command -v skfmt &>/dev/null; then
            skfmt -i "$file_path"
        else
            DOCKER_IMAGE="${DOCKER_IMAGE:-skiplabs/skip:latest}"
            REPO_ROOT="$CLAUDE_PROJECT_DIR"
            REL_PATH="${file_path#"$REPO_ROOT"/}"
            docker run --rm \
                -v "$REPO_ROOT:/work/skjs" \
                -w /work/skjs \
                "$DOCKER_IMAGE" \
                skfmt -i "$REL_PATH"
        fi
        ;;
    *.ts|*.json) npx -y prettier@"$PRETTIER_VERSION" --write "$file_path" ;;
esac
