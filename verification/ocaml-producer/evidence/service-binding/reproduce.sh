#!/usr/bin/env bash
# Reproduce the service-binding evidence: the pipeline (parser -> OCaml -> Lean)
# on the crashing service under today's binding and under the sound binding,
# and on the correct service under the sound binding. Run from the repository
# root after `lake -d verification/lean build` and
# `dune build --root verification/ocaml-producer`.
set -u
EX=verification/ocaml-producer/examples
EV=verification/ocaml-producer/evidence/service-binding
for f in $EX/framework-binding-unsound.ts $EV/crashing-service-sound-binding.ts \
    $EX/framework-binding-sound.ts; do
  echo "--- pipeline $(basename "$f")"
  node verification/ocaml-producer/check.mts "$f" | node -e '
    const d = JSON.parse(require("fs").readFileSync(0, "utf8"));
    console.log(`status: ${d.status} | phase: ${d.phase} | functions: ${JSON.stringify(d.functions ?? null)}`);
    if (d.detail) console.log(`detail: ${d.detail.split("\n")[0].replace(/in \/\S*#/, "in #").slice(0, 160)}`);'
done
