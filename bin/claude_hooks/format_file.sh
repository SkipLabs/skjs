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
    *.sk)        skfmt -i "$file_path" ;;
    *.ts|*.json) npx -y prettier@"$PRETTIER_VERSION" --write "$file_path" ;;
esac
