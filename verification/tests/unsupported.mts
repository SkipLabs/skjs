#!/usr/bin/env node
// Boundary examples must fail for a known unsupported feature, never pass as
// verified. Each goes through the pipeline (parser, OCaml producer, Lean) and
// must be refused with its own reason.
import assert from "node:assert/strict";
import fs from "node:fs";
import { check } from "../ocaml-producer/check.mts";

const dir = "verification/tests/unsupported";
const cases = {
  "in_inherited.ts": "every object inherits it from Object.prototype",
  "instanceof_narrow.ts": "nothing in the file says which prototype a constructor from elsewhere gives its instances",
  "mutable_binding.ts": "a `let` needs an initializer",
};
assert.deepEqual(
  fs
    .readdirSync(dir)
    .filter((f) => f.endsWith(".ts"))
    .sort(),
  Object.keys(cases).sort(),
);
for (const [name, reason] of Object.entries(cases)) {
  const outcome = check(dir + "/" + name);
  try {
    assert.notEqual(
      outcome.status,
      "verified",
      name + " unexpectedly became supported; promote it to a pipeline case",
    );
    assert(
      outcome.status !== "verified" && outcome.detail.includes(reason),
      name + ": " + JSON.stringify(outcome),
    );
    console.log("  unsupported " + name + ": expected boundary");
  } finally {
    fs.rmSync(outcome.artifacts, { recursive: true, force: true });
  }
}
