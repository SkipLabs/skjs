#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import { createHash } from "node:crypto";
import surface from "../tools/claim-text.mts";
import { fileOf, functionOf } from "../tools/skjs-claims.mts";
import {
  claimValue,
  editable,
  editClaim,
  addClaim,
  addFunction,
} from "../report-viewer/candidate.mts";
import { candidateReport, analyse } from "../report-viewer/serve.mts";
import { fromBundle } from "../report-viewer/model.mts";
import { producerMarks } from "../report-viewer/marks.mts";
import type {
  Bundle,
  Candidate,
  ReportFunction,
  Result,
} from "../report-viewer/types.ts";
import type { SkjsClaims, SkjsNamedPoint } from "../tools/skjs-claims.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import type { ShownFunction, Site } from "../report-viewer/model.mts";
import type { ClaimSite } from "../report-viewer/candidate.mts";

/** A candidate in one of the two formats, where the test reads the document
 * back: the editor returns whichever it was given, and these say which. */
type Exported = Extract<Candidate, { format: "skjs" }>;
type Normalized = Extract<Candidate, { format: "source-claims" }>;
const exported = (c: Candidate): SkjsClaims => {
  if (c.format !== "skjs") throw Error("expected a producer candidate");
  return c.claims;
};
const normalizedClaims = (c: Candidate): SourceClaims<number> => {
  if (c.format !== "source-claims")
    throw Error("expected a normalized candidate");
  return c.claims;
};
/** A site as the editor is given one: what kind it is, and where. */
const site = (kind: Site["kind"], pos: [number, number]) => ({ kind, pos });
/** The verifier ran, so the report states results; a report that states none
 * is this test's own setup failing rather than a claim not following. */
const results = (bundle: Bundle): Result[] => {
  if (!bundle.manifest.results) throw Error("this report states no results");
  return bundle.manifest.results;
};
const resultFor = (bundle: Bundle, id: string): Result => {
  const found = results(bundle).find((r) => r.function === id);
  if (!found) throw Error(`this report says nothing about ${id}`);
  return found;
};
const reported = (bundle: Bundle, name: string): ReportFunction => {
  const found = bundle.manifest.functions.find((f) => f.name === name);
  if (!found) throw Error(`this report says nothing about ${name}`);
  return found;
};
const shownIn = (bundle: Bundle, name: string): ShownFunction => {
  const found = fromBundle(bundle).functions.find((f) => f.name === name);
  if (!found) throw Error(`this report shows nothing for ${name}`);
  return found;
};
/** Where a failure attached, which every failing result here names. */
const where = (result: Result) => {
  if (!result.location) throw Error("this result names no place");
  return result.location;
};
process.env.SKJS_BIN = "/no-producer-in-candidate-tests";

const file = "verification/tests/stateful-source/closures.ts";
const source = fs.readFileSync(file, "utf8");
const sourceSha256 = createHash("sha256").update(source).digest("hex");
const claims: SkjsClaims = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const original: Exported = { format: "skjs", file, sourceSha256, claims };
const fn = functionOf(claims, file, "capturedRead");
const expression = fn.exprs.find((e) => source.slice(...e.pos) === "read(null)");
assert(expression);
const item = site("expression", expression.pos);
const wrong = { top: false, atoms: [{ a: "null" }] };
const edited = editClaim(original, fn, item, wrong);
assert.deepEqual(claimValue(edited, fn, item), wrong);
assert.deepEqual(claimValue(original, fn, item), expression.type);
assert.notDeepEqual(claimValue(original, fn, item), wrong);
const env = site("environment", fn.envs[0].pos);
assert.throws(() => editClaim(original, fn, env, {}), /array/);
assert.throws(
  () => editClaim(original, { ...fn, name: "missing" }, item, wrong),
  /function/,
);
const normalized: Normalized = {
  format: "source-claims",
  file,
  sourceSha256,
  claims: {
    file,
    sourceSha256,
    types: [],
    functions: [
      {
        name: fn.name,
        namePos: fn.namePos,
        params: [],
        result: [0],
        entries: [
          {
            start: env.pos[0],
            bindings: [{ name: "x", type: [0], current: null }],
          },
        ],
        expressions: [{ pos: item.pos, type: [1, 2], current: null }],
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
  const tabled: Normalized = structuredClone(normalized);
  tabled.claims.types = [["nul"], [{ boolLit: { value: true } }], [{ boolLit: { value: false } }], ["undef"]];
  tabled.claims.types.push([{ refs: { first: [["value", [1, 2]]], rest: [], views: [] } }]);
  const observed = [{ name: "cell", type: [4], current: [["value", [1]]] }];
  const withObservation = editClaim(tabled, fn, env, observed);
  assert.deepEqual(claimValue(withObservation, fn, env), observed);
  assert.deepEqual(
    claimValue(
      editClaim(withObservation, fn, env, claimValue(withObservation, fn, env)),
      fn,
      env,
    ),
    observed,
  );
  assert.deepEqual(
    claimValue(
      editClaim(withObservation, fn, env, [{ ...observed[0], current: null }]),
      fn,
      env,
    ),
    [{ name: "cell", type: [4], current: null }],
  );
  for (const current of ["true", ["1"], [-1], [1.5], [5]])
    assert.throws(() =>
      editClaim(tabled, fn, env, [{ name: "cell", type: [4], current }]),
    );
  tabled.claims.types.pop();
  assert.deepEqual(editable(tabled, fn, item), {
    top: false,
    atoms: [{ a: "boolean" }],
  });
  const boolean = { top: false, atoms: [{ a: "boolean" }] };
  const cell = {
    top: false,
    atoms: [{ a: "record", fields: [{ name: "value", optional: false, read: { top: false, atoms: [{ a: "booleanlit", v: "true" }] }, write: boolean }] }],
  };
  const held = normalizedClaims(editClaim(tabled, fn, item, cell));
  assert.deepEqual(held.functions[0].expressions[0], { pos: item.pos, type: [4], current: [["value", [1]]] });
  assert.deepEqual(held.types[4], [{ refs: { first: [["value", [1, 2]]], rest: [], views: [] } }]);
  assert.equal(
    surface.printType(
      editable({ ...tabled, claims: held }, fn, item),
    ).text,
    "{ value: boolean = (true) }",
  );
  assert.equal(tabled.claims.types.length, 4);
}
// Native signature edits preserve every parameter, including a true empty list.
for (const params of [
  [],
  [{top: false, atoms: [{a: "boolean"}]}, {top: false, atoms: [{a: "null"}]}],
]) {
  const tabled: Normalized = structuredClone(normalized);
  tabled.claims.types = [["nul"], [{boolLit: {value: true}}], [{boolLit: {value: false}}], ["undef"]];
  const arrow = {top: false, atoms: [{a: "function", this: {top: true, atoms: []}, params,
    result: {top: false, atoms: [{a: "boolean"}]}, construct: "unknown", array: "unknown"}]};
  const changed = editClaim(tabled, fn, item, arrow);
  // The receiver is lowered first: the top row at 4, the signature at 5.
  assert.deepEqual(normalizedClaims(changed).types[4], ["top"]);
  assert.deepEqual(normalizedClaims(changed).types[5], [{arrs: {arrows: [[[4], [params.length ? [[1,2],[0]] : [],[1,2]]]]}}]);
  assert.deepEqual(editable(changed, fn, item), arrow);
}

(async () => {
  const preview = await candidateReport(edited, false);
  assert.equal(preview.manifest.results, null);
  assert.equal(preview.manifest.producer, "manual candidate");
  const checked = await candidateReport(original, true);
  assert(results(checked).every((r) => r.status === "verified"));
  const rejected = await candidateReport(edited, true);
  const target = reported(rejected, fn.name);
  assert.equal(resultFor(rejected, target.id).status, "not-established");
  assert.deepEqual(where(resultFor(rejected, target.id)), {
    kind: "expression-obligation",
    pos: expression.pos,
  });
  const edgeClaims: Exported = structuredClone(original);
  const edgeFn = functionOf(edgeClaims.claims, file, fn.name);
  edgeFn.envs[2].vars[0].type = wrong;
  const edgeReport = await candidateReport(edgeClaims, true);
  const edgePlace = where(resultFor(edgeReport, target.id));
  assert.equal(edgePlace.kind, "expression-obligation");
  // The statement is checked from its supplied environment. Its cell read
  // fails locally when that environment calls the receiver null.
  assert(edgePlace.pos);
  assert.equal(source.slice(...edgePlace.pos), "cell");
  const seeds = claimValue(original, fn, env);
  assert(Array.isArray(seeds));
  const badEnv = editClaim(
    original,
    fn,
    env,
    seeds.map((b: SkjsNamedPoint) =>
      b.name === "seed" ? { ...b, type: { unsupported: true } } : b,
    ),
  );
  const envReport = await candidateReport(badEnv, true);
  assert.deepEqual(where(resultFor(envReport, target.id)), {
    kind: "unavailable-type-claim",
    start: env.pos[0],
    binding: "seed",
  });
  const outsideFile = "verification/tests/unsupported/in_inherited.ts";
  const outsideSource = fs.readFileSync(outsideFile, "utf8");
  const nameStart = outsideSource.indexOf("describe");
  const condition = '"toString" in x';
  const conditionStart = outsideSource.indexOf(condition);
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
                pos: [conditionStart, conditionStart + condition.length],
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
  assert.deepEqual(where(results(outsideReport)[0]), {
    kind: "source-limitation",
    pos: [conditionStart, conditionStart + condition.length],
  });
  // Repair missing information in a sound program without collecting again.
  const incomplete: Exported = structuredClone(original);
  const incompleteFn = functionOf(incomplete.claims, file, fn.name);
  incompleteFn.envs = incompleteFn.envs.filter(
    (e) => JSON.stringify(e.pos) !== JSON.stringify(env.pos),
  );
  incompleteFn.exprs = incompleteFn.exprs.filter(
    (e) => JSON.stringify(e.pos) !== JSON.stringify(item.pos),
  );
  const partial = await candidateReport(incomplete, true);
  // Sites are addressed through the shown function, as the reader addresses them.
  const partialFn = shownIn(partial, fn.name);
  // A claim is added at a site addressed by what belongs there, as the reader does.
  const unclaimedAt = (f: ShownFunction, claims: string): ClaimSite[] =>
    f.sites.flatMap((s) =>
      s.kind === "unclaimed" && s.claims === claims
        ? [{ kind: s.claims, pos: s.pos }]
        : [],
    );
  assert.equal(resultFor(partial, partialFn.id).status, "not-established");
  const expressionSite = unclaimedAt(partialFn, "expression").find(
    (s) => JSON.stringify(s.pos) === JSON.stringify(item.pos),
  );
  const entrySite = unclaimedAt(partialFn, "environment").find(
    (s) => s.pos[0] === env.pos[0],
  );
  assert(expressionSite && entrySite);
  const unclaimed = partialFn.sites.filter((s) => s.kind === "unclaimed");
  assert(!unclaimed.some((s) => s.pos[0] === source.indexOf("unit: null") + 6));
  assert(!unclaimed.some((s) => s.pos[0] === fn.namePos[0]));
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
  assert(results(repairedReport).every((r) => r.status === "verified"));
  const repairedFn = reported(repairedReport, fn.name);
  assert(
    !(repairedFn.missingSites ?? []).some(
      (s) => JSON.stringify(s.pos) === JSON.stringify(item.pos),
    ),
  );
  assert.throws(
    () => claimValue(incomplete, fn, item),
    /no matching expression/,
  );
  const emptyNormalized: Normalized = structuredClone(normalized);
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
  const withoutFunction: Exported = structuredClone(original);
  const withoutFile = fileOf(withoutFunction.claims, file);
  withoutFile.functions = withoutFile.functions.filter(
    (f) => f.name !== fn.name,
  );
  const missingReport = await candidateReport(withoutFunction, false);
  const missingFunction = (
    missingReport.manifest.missingFunctions ?? []
  ).find((f) => f.name === fn.name);
  assert(missingFunction);
  const missingModel = shownIn(missingReport, fn.name);
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
  let restored: Candidate = addFunction(withoutFunction, missingModel, contract);
  assert.throws(
    () => addFunction(restored, missingModel, contract),
    /already exists/,
  );
  assert.equal(
    fileOf(withoutFunction.claims, file).functions.some(
      (f) => f.name === fn.name,
    ),
    false,
  );
  for (const e of fn.exprs) {
    const site = unclaimedAt(missingModel, "expression").find(
      (s) => JSON.stringify(s.pos) === JSON.stringify(e.pos),
    );
    assert(site, "missing expression repair site " + e.pos);
    restored = addClaim(restored, missingModel, site, e.type);
  }
  for (const e of fn.envs) {
    const site = unclaimedAt(missingModel, "environment").find(
      (s) => s.pos[0] === e.pos[0],
    );
    assert(site, "missing environment repair site " + e.pos);
    restored = addClaim(restored, missingModel, site, e.vars);
  }
  const restoredReport = await candidateReport(restored, true);
  assert(results(restoredReport).every((r) => r.status === "verified"));
  assert(
    !(restoredReport.manifest.missingFunctions ?? []).some(
      (f) => f.name === fn.name,
    ),
  );
  const wrongContract = structuredClone(restored);
  functionOf(exported(wrongContract), file, fn.name).retType = wrong;
  const wrongReport = await candidateReport(wrongContract, true);
  assert(
    results(wrongReport).some(
      (r) =>
        r.status === "not-established" &&
        /return type differs/.test(r.detail ?? ""),
    ),
  );
  const normalizedFunction = addFunction(
    { ...normalized, claims: { ...normalized.claims, functions: [] } },
    missingModel,
    {
      params: fn.params.map((p) => ({ name: p.name, type: [1, 2] })),
      result: [1, 2],
    },
  );
  assert.deepEqual(normalizedClaims(normalizedFunction).functions[0], {
    name: fn.name,
    namePos: fn.namePos,
    params: fn.params.map((p) => ({ name: p.name, type: [1, 2], current: null })),
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
assert(genericCandidate, "this report carries no candidate to edit");
const genericFn = normalizedClaims(genericCandidate).functions[0];
const genericItem = site("expression", genericFn.expressions[0].pos);
const parameterT = {top:false,atoms:[{a:"param",name:"T"}]};
assert.equal(genericBundle.manifest.functions[0].collection?.completion,"complete");
assert.deepEqual(editable(genericCandidate,genericFn,genericItem),parameterT);
assert.deepEqual(claimValue(editClaim(genericCandidate,genericFn,genericItem,parameterT),genericFn,genericItem),{param:"T"});
const genericModel = fromBundle(genericBundle);
assert.equal(genericModel.functions[0].collection,"complete");
assert.equal(genericModel.diagnostics, "");

// A TS rejection must survive exporter -> collector -> report -> source mark,
// even when its generic closure cannot be exported as a claim.
const rejectedBundle = await analyse("verification/ocaml-producer/examples/generic-dependent-inference.ts", "tsc");
const rejectedModel = fromBundle(rejectedBundle);
assert.match(rejectedModel.diagnostics ?? "", /TS2345: Argument of type 'boolean'/);
const diagnosticMarks = producerMarks(rejectedModel);
assert.equal(diagnosticMarks.length, 1);
assert.equal(rejectedModel.source.slice(...diagnosticMarks[0].pos), "flag");
