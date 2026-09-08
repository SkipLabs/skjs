#!/usr/bin/env node
// Exact callback contracts, real SKJS exports, and a captured-refinement witness.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const vm = require("node:vm");
const { spawnSync } = require("node:child_process");
const ts = require("../tools/node_modules/typescript");
const [
  astPath,
  claimsPath,
  file,
  verifier,
  badAstPath,
  badClaimsPath,
  badFile,
] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath));
const claims = JSON.parse(fs.readFileSync(claimsPath));
const tmp = fs.mkdtempSync(os.tmpdir() + "/primitive-callbacks-");
const clone = structuredClone;
const nul = { top: false, atoms: [{ a: "null" }] };
let passed = 0;
function run(mode, a, c, key = file, evidence) {
  fs.writeFileSync(tmp + "/ast.json", JSON.stringify(a));
  fs.writeFileSync(tmp + "/claims.json", JSON.stringify(c));
  if (evidence)
    fs.writeFileSync(tmp + "/evidence.json", JSON.stringify(evidence));
  const args = [
    mode,
    tmp + "/ast.json",
    tmp + "/claims.json",
    key,
    tmp + "/evidence.json",
  ];
  if (mode.startsWith("--produce")) args.push("10");
  const r = spawnSync(verifier, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
}
function expect(name, r, accept, reason = "") {
  assert.equal(r.status === 0, accept, name + ": " + r.stderr);
  assert((r.stdout + r.stderr).includes(reason), name + ": " + r.stderr);
  console.log("  " + name + ": OK");
  passed++;
}
function runtime(path) {
  const context = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(path, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
    context,
    { timeout: 1000 },
  );
  return context;
}
try {
  expect(
    "primitive callback source production",
    run("--produce-stateful-source", ast, claims),
    true,
  );
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json"));
  expect(
    "primitive callback independent consumption",
    run("--check-stateful-source", ast, claims, file, evidence),
    true,
  );
  const exported = spawnSync(
    verifier,
    ["--export-source-claims", astPath, claimsPath, file],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exported.status, 0, exported.stderr);
  const normalized = JSON.parse(exported.stdout).claims;
  assert.equal(normalized.profile, "stateful-source-75-v2");
  expect(
    "normalized primitive domains round-trip",
    run("--produce-source-claims", ast, normalized),
    true,
  );
  const normalizedEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json"),
  );
  expect(
    "normalized independent consumption",
    run("--check-source-claims", ast, normalized, file, normalizedEvidence),
    true,
  );
  const a = clone(ast),
    c = clone(claims);
  const f = a.functions.find((f) => f.name === "booleanIdentity");
  const call = f.body.at(-1).e;
  const pos = call.arg.pos;
  call.arg = { k: "lit", pos, lit: { a: "null" } };
  c
    .find((f) => f.file === file)
    .functions.find((f) => f.name === "booleanIdentity")
    .exprs.find((e) => JSON.stringify(e.pos) === JSON.stringify(pos)).type =
    nul;
  expect(
    "null does not satisfy Boolean callback domain",
    run("--produce-stateful-source", a, c),
    false,
    "evidence search failed",
  );
  expect(
    "old certificate cannot justify changed call",
    run("--check-stateful-source", a, c, file, evidence),
    false,
  );
  const bad = JSON.parse(fs.readFileSync(badClaimsPath)),
    ba = JSON.parse(fs.readFileSync(badAstPath));
  expect(
    "original refined reference hits invariant boundary",
    run("--produce-stateful-source", ba, bad, badFile),
    false,
    "read and write types do not describe the same invariant",
  );
  // Soundly forget only reference read refinements, retaining every expression claim.
  // This is a manual candidate experiment, not acceptance of the original export.
  const weakened = clone(bad);
  function forget(x) {
    if (!x || typeof x !== "object") return;
    if (x.a === "record")
      for (const field of x.fields) field.read = clone(field.write);
    for (const value of Object.values(x)) forget(value);
  }
  forget(weakened);
  const rejected = run("--produce-stateful-source", ba, weakened, badFile);
  expect(
    "stale singleton read fails a typing obligation",
    rejected,
    false,
    "source expression obligation at",
  );
  assert(rejected.stderr.includes("evidence search failed"));
  const body = ba.functions[0].body;
  const stale = body.find((s) => s.k === "if").then.at(-1).e.pos;
  assert(rejected.stderr.includes(`[${stale[0]},${stale[1]})`));
  const goodRuntime = runtime(file),
    badRuntime = runtime(badFile);
  assert.equal(badRuntime.staleCapturedCell(true), false);
  assert.equal(badRuntime.staleCapturedCell(false), true);
  for (const seed of [true, false]) {
    assert.equal(goodRuntime.capturedWriter(seed), false);
    assert.equal(goodRuntime.stableSnapshot(seed), true);
    assert.equal(goodRuntime.booleanIdentity(seed), seed);
  }
  for (const value of [null, true, false])
    assert.equal(goodRuntime.unionIdentity(value), value);
  assert.equal(goodRuntime.returnedWriter()(false), false);
  assert.equal(goodRuntime.narrowerCallContract(), true);
  console.log("  runtime witness and stable-snapshot counterpart: OK");
  console.log(`Primitive callbacks: ${passed + 1} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
