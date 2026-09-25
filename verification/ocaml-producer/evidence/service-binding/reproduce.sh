#!/usr/bin/env bash
# Reproduce the service-binding evidence: tsc and the pipeline on today's
# binding (framework-binding-unsound.ts) and the sound binding
# (framework-binding-sound.ts). Run from the repository root after
# `lake -d verification/lean build` and `dune build --root verification/ocaml-producer`.
set -u
EX=verification/ocaml-producer/examples
TSC=verification/tools/node_modules/.bin/tsc
echo "tsc: $($TSC --version)"
for f in $EX/framework-binding-unsound.ts $EX/framework-binding-sound.ts; do
  echo "--- tsc --strict $(basename "$f")"
  $TSC --ignoreConfig --noEmit --strict --noUncheckedIndexedAccess --target ES2021 \
    --module Node16 --moduleResolution Node16 "$f"
  echo "exit $?"
done
for f in framework-binding-unsound framework-binding-sound; do
  echo "--- pipeline $f.ts"
  node verification/ocaml-producer/check.mts "$EX/$f.ts" | node -e '
    const d = JSON.parse(require("fs").readFileSync(0, "utf8"));
    console.log(`status: ${d.status} | phase: ${d.phase} | functions: ${JSON.stringify(d.functions ?? null)}`);
    if (d.detail) console.log(`detail: ${d.detail.split("\n")[0].slice(0, 160)}`);'
done
