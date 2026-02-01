#!/bin/bash
set -e

cd "$(dirname "$0")"

echo "=== Installing dependencies ==="
npm install --silent
npm install --silent @skipruntime/server @skipruntime/helpers

echo "=== Building ==="
npm run build

echo "=== Starting service ==="
node dist/main.js &
SERVER_PID=$!
trap 'kill $SERVER_PID 2>/dev/null' EXIT

sleep 2

echo "=== Running test ==="
node dist/test.js

echo "=== Done ==="
