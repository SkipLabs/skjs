#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const { createHash } = require("node:crypto");
const { claimValue, editClaim } = require("../report-viewer/candidate.js");
process.env.SKJS_BIN = "/no-producer-in-candidate-tests";
const { candidateReport } = require("../report-viewer/serve.js");
const file = "verification/tests/stateful-source/closures.ts";
const source = fs.readFileSync(file, "utf8");
const sourceSha256 = createHash("sha256").update(source).digest("hex");
const claims = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const original = { format: "skjs", file, sourceSha256, claims };
const fn = claims
  .find((f) => f.file === file)
  .functions.find((f) => f.name === "capturedRead");
const expression = fn.exprs.find(
  (e) => source.slice(...e.pos) === "read(null)",
);
assert(expression);
const item = { kind: "expression", pos: expression.pos };
const wrong = { top: false, atoms: [{ a: "null" }] };
const edited = editClaim(original, fn, item, wrong);
assert.deepEqual(claimValue(edited, fn, item), wrong);
assert.deepEqual(claimValue(original, fn, item), expression.type);
assert.notDeepEqual(claimValue(original, fn, item), wrong);
const env = { kind: "environment", pos: fn.envs[0].pos };
assert.throws(() => editClaim(original, fn, env, {}), /array/);
assert.throws(
  () => editClaim(original, { ...fn, name: "missing" }, item, wrong),
  /function/,
);
const normalized = {
  format: "source-claims",
  file,
  sourceSha256,
  claims: {
    functions: [
      {
        name: fn.name,
        namePos: fn.namePos,
        entries: [{ start: env.pos[0], bindings: [{ name: "x", type: [0] }] }],
        expressions: [{ pos: item.pos, type: [1, 2] }],
      },
    ],
  },
};
assert.deepEqual(claimValue(editClaim(normalized, fn, item, [0]), fn, item), [
  0,
]);
assert.deepEqual(
  claimValue(
    editClaim(normalized, fn, env, [{ name: "x", type: [1] }]),
    fn,
    env,
  ),
  [{ name: "x", type: [1] }],
);
(async () => {
  const preview = await candidateReport(edited, false);
  assert.equal(preview.manifest.results, null);
  assert.equal(preview.manifest.producer, "manual candidate");
  const checked = await candidateReport(original, true);
  assert(checked.manifest.results.every((r) => r.status === "verified"));
  const rejected = await candidateReport(edited, true);
  const target = rejected.manifest.functions.find((f) => f.name === fn.name);
  assert.equal(
    rejected.manifest.results.find((r) => r.function === target.id).status,
    "not-established",
  );
  assert.deepEqual(
    rejected.manifest.results.find((r) => r.function === target.id).location,
    { kind: "expression-obligation", pos: expression.pos },
  );
  await assert.rejects(
    candidateReport({ ...original, sourceSha256: "stale" }, true),
    /Source changed/,
  );
  assert.equal(fs.readFileSync(file, "utf8"), source);
  console.log(
    "Candidate editor: immutable baseline, preview, fresh verification, false claim and stale source checks passed",
  );
})().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
