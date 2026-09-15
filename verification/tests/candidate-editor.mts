#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import { createHash } from "node:crypto";
import surface from "../tools/claim-text.mts";
import {
  claimValue,
  editable,
  editClaim,
  addClaim,
  addFunction,
} from "../report-viewer/candidate.mts";
import { candidateReport, analyse } from "../report-viewer/serve.mts";
import { fromBundle } from "../report-viewer/model.mts";
process.env.SKJS_BIN = "/no-producer-in-candidate-tests";

const file = "verification/tests/stateful-source/closures.ts";
const source = fs.readFileSync(file, "utf8");
const sourceSha256 = createHash("sha256").update(source).digest("hex");
const claims = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const original = { format: "skjs", file, sourceSha256, claims };
const fn = claims
  .find((f: any) => f.file === file)
  .functions.find((f: any) => f.name === "capturedRead");
const expression = fn.exprs.find(
  (e: any) => source.slice(...e.pos) === "read(null)",
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
  [{ name: "x", type: [1], current: null }],
);
// A normalized claim is shown lifted into the structural encoding the one
// editor speaks, and lowered back on apply, interning into the document's own
// table the rows the edit needs.
{
  const tabled: any = structuredClone(normalized);
  tabled.claims.types = [["nul"], [{ boolLit: { value: true } }], [{ boolLit: { value: false } }], ["undef"]];
  assert.deepEqual(editable(tabled, fn, item), { top: false, atoms: [{ a: "boolean" }] });
  const boolean = { top: false, atoms: [{ a: "boolean" }] };
  const cell = {
    top: false,
    atoms: [{ a: "record", fields: [{ name: "value", optional: false, read: { top: false, atoms: [{ a: "booleanlit", v: "true" }] }, write: boolean }] }],
  };
  const held = editClaim(tabled, fn, item, cell);
  assert.deepEqual(held.claims.functions[0].expressions[0], { pos: item.pos, type: [4], current: [1] });
  assert.deepEqual(held.claims.types[4], [{ refs: { first: [1, 2], rest: [] } }]);
  assert.equal(surface.printType(editable(held, fn, item)).text, "{ value: boolean = (true) }");
  assert.equal(tabled.claims.types.length, 4);
}
// Native signature edits preserve every parameter, including a true empty list.
for (const params of [
  [],
  [{top: false, atoms: [{a: "boolean"}]}, {top: false, atoms: [{a: "null"}]}],
]) {
  const tabled: any = structuredClone(normalized);
  tabled.claims.types = [["nul"], [{boolLit: {value: true}}], [{boolLit: {value: false}}], ["undef"]];
  const arrow = {top: false, atoms: [{a: "function", params,
    result: {top: false, atoms: [{a: "boolean"}]}, construct: "unknown", array: "unknown"}]};
  const changed = editClaim(tabled, fn, item, arrow);
  assert.deepEqual(changed.claims.types[4], [{arrs: {arrows: [[params.length ? [[1,2],[0]] : [],[1,2]]]}}]);
  assert.deepEqual(editable(changed, fn, item), arrow);
}

(async () => {
  const preview = await candidateReport(edited, false);
  assert.equal(preview.manifest.results, null);
  assert.equal(preview.manifest.producer, "manual candidate");
  const checked = await candidateReport(original, true);
  assert(checked.manifest.results.every((r: any) => r.status === "verified"));
  const rejected = await candidateReport(edited, true);
  const target = rejected.manifest.functions.find((f: any) => f.name === fn.name);
  assert.equal(
    rejected.manifest.results.find((r: any) => r.function === target.id).status,
    "not-established",
  );
  assert.deepEqual(
    rejected.manifest.results.find((r: any) => r.function === target.id).location,
    { kind: "expression-obligation", pos: expression.pos },
  );
  const edgeClaims = structuredClone(original);
  const edgeFn = edgeClaims.claims
    .find((f: any) => f.file === file)
    .functions.find((f: any) => f.name === fn.name);
  edgeFn.envs[2].vars[0].type = wrong;
  const edgeReport = await candidateReport(edgeClaims, true);
  const edgeResult = edgeReport.manifest.results.find(
    (r: any) => r.function === target.id,
  );
  assert.equal(edgeResult.location.kind, "expression-obligation");
  // The statement is checked from its supplied environment. Its cell read
  // fails locally when that environment calls the receiver null.
  assert.equal(source.slice(...edgeResult.location.pos), "cell");
  const badEnv = editClaim(
    original,
    fn,
    env,
    claimValue(original, fn, env).map((b: any) =>
      b.name === "seed" ? { ...b, type: { unsupported: true } } : b,
    ),
  );
  const envReport = await candidateReport(badEnv, true);
  assert.deepEqual(
    envReport.manifest.results.find((r: any) => r.function === target.id).location,
    { kind: "unavailable-type-claim", start: env.pos[0], binding: "seed" },
  );
  const outsideFile = "verification/tests/unsupported/typeof_narrow.ts";
  const outsideSource = fs.readFileSync(outsideFile, "utf8");
  const nameStart = outsideSource.indexOf("describe");
  const conditionStart = outsideSource.indexOf("typeof x");
  const outsideReport = await candidateReport(
    {
      format: "source-claims",
      file: outsideFile,
      sourceSha256: createHash("sha256").update(outsideSource).digest("hex"),
      claims: {
        types: [
          ["nul"],
          [{ boolLit: { value: true } }],
          [{ boolLit: { value: false } }],
          ["undef"],
        ],
        file: outsideFile,
        sourceSha256: createHash("sha256").update(outsideSource).digest("hex"),
        functions: [
          {
            name: "describe",
            namePos: [nameStart, nameStart + 8],
            params: [],
            result: [0],
            entries: [],
            expressions: [
              {
                pos: [conditionStart, conditionStart + 8],
                type: [1, 2],
                current: null,
              },
            ],
          },
        ],
      },
    },
    true,
  );
  assert.deepEqual(outsideReport.manifest.results[0].location, {
    kind: "source-limitation",
    pos: [conditionStart, conditionStart + 8],
  });
  // Repair missing information in a sound program without collecting again.
  const incomplete = structuredClone(original);
  const incompleteFn = incomplete.claims
    .find((f: any) => f.file === file)
    .functions.find((f: any) => f.name === fn.name);
  incompleteFn.envs = incompleteFn.envs.filter(
    (e: any) => JSON.stringify(e.pos) !== JSON.stringify(env.pos),
  );
  incompleteFn.exprs = incompleteFn.exprs.filter(
    (e: any) => JSON.stringify(e.pos) !== JSON.stringify(item.pos),
  );
  const partial = await candidateReport(incomplete, true);
  // Sites are addressed through the shown function, as the reader addresses them.
  const partialFn = fromBundle(partial).functions.find((f: any) => f.name === fn.name)!;
  // A claim is added at a site addressed by what belongs there, as the reader does.
  const unclaimedAt = (f: any, claims: string) =>
    f.sites
      .filter((s: any) => s.kind === "unclaimed" && s.claims === claims)
      .map((s: any) => ({ kind: s.claims, pos: s.pos }));
  assert.equal(
    partial.manifest.results.find((r: any) => r.function === partialFn.id).status,
    "not-established",
  );
  const expressionSite = unclaimedAt(partialFn, "expression").find(
    (s: any) => JSON.stringify(s.pos) === JSON.stringify(item.pos),
  );
  const entrySite = unclaimedAt(partialFn, "environment").find(
    (s: any) => s.pos[0] === env.pos[0],
  );
  assert(expressionSite && entrySite);
  const unclaimed = partialFn.sites.filter((s: any) => s.kind === "unclaimed");
  assert(!unclaimed.some((s: any) => s.pos[0] === source.indexOf("unit: null") + 6));
  assert(!unclaimed.some((s: any) => s.pos[0] === fn.namePos[0]));
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
  assert(repairedReport.manifest.results.every((r: any) => r.status === "verified"));
  const repairedFn = repairedReport.manifest.functions.find(
    (f: any) => f.name === fn.name,
  );
  assert(
    !repairedFn.missingSites.some(
      (s: any) => JSON.stringify(s.pos) === JSON.stringify(item.pos),
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
  // Repair a whole missing function, keeping its contract separate from point claims.
  const withoutFunction = structuredClone(original);
  withoutFunction.claims.find((f: any) => f.file === file).functions =
    withoutFunction.claims
      .find((f: any) => f.file === file)
      .functions.filter((f: any) => f.name !== fn.name);
  const missingReport = await candidateReport(withoutFunction, false);
  const missingFunction = missingReport.manifest.missingFunctions.find(
    (f: any) => f.name === fn.name,
  );
  assert(missingFunction);
  const missingModel = fromBundle(missingReport).functions.find((f: any) => f.name === fn.name)!;
  assert.equal(missingModel.candidateMissing, true);
  const contract = { params: fn.params, result: fn.retType };
  assert.throws(
    () =>
      addFunction(withoutFunction, missingModel, { ...contract, params: [] }),
    /source order/,
  );
  assert.throws(
    () =>
      addFunction(
        withoutFunction,
        { ...missingModel, candidateMissing: false },
        contract,
      ),
    /without a candidate/,
  );
  let restored = addFunction(withoutFunction, missingModel, contract);
  assert.throws(
    () => addFunction(restored, missingModel, contract),
    /already exists/,
  );
  assert.equal(
    withoutFunction.claims
      .find((f: any) => f.file === file)
      .functions.some((f: any) => f.name === fn.name),
    false,
  );
  for (const e of fn.exprs) {
    const site = unclaimedAt(missingModel, "expression").find(
      (s: any) => JSON.stringify(s.pos) === JSON.stringify(e.pos),
    );
    assert(site, "missing expression repair site " + e.pos);
    restored = addClaim(restored, missingModel, site, e.type);
  }
  for (const e of fn.envs) {
    const site = unclaimedAt(missingModel, "environment").find(
      (s: any) => s.pos[0] === e.pos[0],
    );
    assert(site, "missing environment repair site " + e.pos);
    restored = addClaim(restored, missingModel, site, e.vars);
  }
  const restoredReport = await candidateReport(restored, true);
  assert(restoredReport.manifest.results.every((r: any) => r.status === "verified"));
  assert(
    !restoredReport.manifest.missingFunctions.some((f: any) => f.name === fn.name),
  );
  const wrongContract = structuredClone(restored);
  wrongContract.claims
    .find((f: any) => f.file === file)
    .functions.find((f: any) => f.name === fn.name).retType = wrong;
  const wrongReport = await candidateReport(wrongContract, true);
  assert(
    wrongReport.manifest.results.some(
      (r: any) =>
        r.status === "not-established" && /return type differs/.test(r.detail),
    ),
  );
  const normalizedFunction = addFunction(
    { ...normalized, claims: { functions: [] } },
    missingModel,
    {
      params: fn.params.map((p: any) => ({ name: p.name, type: [1, 2] })),
      result: [1, 2],
    },
  );
  assert.deepEqual(normalizedFunction.claims.functions[0], {
    name: fn.name,
    namePos: fn.namePos,
    params: fn.params.map((p: any) => ({ name: p.name, type: [1, 2], current: null })),
    result: [1, 2],
    entries: [],
    expressions: [],
  });
  await assert.rejects(
    candidateReport({ ...original, sourceSha256: "stale" }, true),
    /Source changed/,
  );
  assert.equal(fs.readFileSync(file, "utf8"), source);
  console.log(
    "Candidate editor: immutable baseline, preview, fresh verification, false claim, stale source, missing-claim and whole-function repair checks passed",
  );
})().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});

// Normalized generic edits retain binder identity, and TS outcomes survive collection.
const genericBundle = await analyse("verification/tests/stateful-source/generic-identity.ts", "tsc");
const genericCandidate = genericBundle.candidate;
const genericFn = genericCandidate.claims.functions[0];
const genericItem = {kind:"expression",pos:genericFn.expressions[0].pos};
const parameterT = {top:false,atoms:[{a:"param",name:"T"}]};
assert.equal(genericBundle.manifest.functions[0].collection.completion,"complete");
assert.deepEqual(editable(genericCandidate,genericFn,genericItem),parameterT);
assert.deepEqual(claimValue(editClaim(genericCandidate,genericFn,genericItem,parameterT),genericFn,genericItem),{param:"T"});
const genericModel = fromBundle(genericBundle);
assert.equal(genericModel.functions[0].collection,"complete");
