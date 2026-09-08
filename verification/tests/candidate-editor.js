#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const { createHash } = require("node:crypto");
const {
  claimValue,
  editClaim,
  addClaim,
} = require("../report-viewer/candidate.js");
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
  // Repair missing information in a sound program without collecting again.
  const incomplete = structuredClone(original);
  const incompleteFn = incomplete.claims
    .find((f) => f.file === file)
    .functions.find((f) => f.name === fn.name);
  incompleteFn.envs = incompleteFn.envs.filter(
    (e) => JSON.stringify(e.pos) !== JSON.stringify(env.pos),
  );
  incompleteFn.exprs = incompleteFn.exprs.filter(
    (e) => JSON.stringify(e.pos) !== JSON.stringify(item.pos),
  );
  const partial = await candidateReport(incomplete, true);
  const partialFn = partial.manifest.functions.find((f) => f.name === fn.name);
  assert.equal(
    partial.manifest.results.find((r) => r.function === partialFn.id).status,
    "not-established",
  );
  const expressionSite = partialFn.missingSites.find(
    (s) =>
      s.kind === "expression" &&
      JSON.stringify(s.pos) === JSON.stringify(item.pos),
  );
  const entrySite = partialFn.missingSites.find(
    (s) => s.kind === "environment" && s.pos[0] === env.pos[0],
  );
  assert(expressionSite && entrySite);
  assert(
    !partialFn.missingSites.some(
      (s) => s.pos[0] === source.indexOf("unit: null") + 6,
    ),
  );
  assert(!partialFn.missingSites.some((s) => s.pos[0] === fn.namePos[0]));
  let repaired = addClaim(
    incomplete,
    partialFn,
    expressionSite,
    expression.type,
  );
  repaired = addClaim(
    repaired,
    partialFn,
    entrySite,
    claimValue(original, fn, env),
  );
  assert.throws(
    () => addClaim(repaired, partialFn, entrySite, []),
    /already exists/,
  );
  assert.throws(
    () =>
      addClaim(
        incomplete,
        partialFn,
        { kind: "expression", pos: [1, 2] },
        wrong,
      ),
    /Choose a missing site/,
  );
  assert.throws(() => addClaim(incomplete, partialFn, entrySite, {}), /array/);
  const repairedReport = await candidateReport(repaired, true);
  assert(repairedReport.manifest.results.every((r) => r.status === "verified"));
  const repairedFn = repairedReport.manifest.functions.find(
    (f) => f.name === fn.name,
  );
  assert(
    !repairedFn.missingSites.some(
      (s) => JSON.stringify(s.pos) === JSON.stringify(item.pos),
    ),
  );
  assert.throws(
    () => claimValue(incomplete, fn, item),
    /no matching expression/,
  );
  const emptyNormalized = structuredClone(normalized);
  emptyNormalized.claims.functions[0].expressions = [];
  emptyNormalized.claims.functions[0].entries = [];
  const normalizedRepair = addClaim(
    addClaim(emptyNormalized, partialFn, entrySite, []),
    partialFn,
    expressionSite,
    [0],
  );
  assert.deepEqual(claimValue(normalizedRepair, fn, item), [0]);
  assert.deepEqual(claimValue(normalizedRepair, fn, env), []);
  await assert.rejects(
    candidateReport({ ...original, sourceSha256: "stale" }, true),
    /Source changed/,
  );
  assert.equal(fs.readFileSync(file, "utf8"), source);
  console.log(
    "Candidate editor: immutable baseline, preview, fresh verification, false claim, stale source and missing-claim repair checks passed",
  );
})().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
