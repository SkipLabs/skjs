#!/usr/bin/env node
// Null predicates are checked independently; graph-edge refinements remain gated.
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
  guardAstPath,
  guardClaimsPath,
  guardFile,
] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath));
const claims = JSON.parse(fs.readFileSync(claimsPath));
const tmp = fs.mkdtempSync(os.tmpdir() + "/null-tests-");
const fn = (c) =>
  c.find((f) => f.file === file).functions.find((f) => f.name === "isNull");
let passed = 0;
function run(mode, a, c, evidence, key = file) {
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
try {
  expect(
    "null predicate production",
    run("--produce-stateful-source", ast, claims),
    true,
  );
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json"));
  expect(
    "null predicate independent consumption",
    run("--check-stateful-source", ast, claims, evidence),
    true,
  );
  const exported = spawnSync(
    verifier,
    ["--export-source-claims", astPath, claimsPath, file],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exported.status, 0, exported.stderr);
  const normalized = JSON.parse(exported.stdout).claims;
  expect(
    "normalized null predicate production",
    run("--produce-source-claims", ast, normalized),
    true,
  );
  const normalizedEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json"),
  );
  expect(
    "normalized null predicate consumption",
    run("--check-source-claims", ast, normalized, normalizedEvidence),
    true,
  );
  for (const [name, mutate, reason] of [
    [
      "null result claim cannot invent true",
      (a, c) => {
        fn(c).exprs.find(
          (e) => e.pos[0] === a.functions[0].body[0].e.pos[0],
        ).type = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
      },
      "evidence search failed",
    ],
    [
      "null literal operand claim required",
      (a, c) => {
        const pos = a.functions[0].body[0].e.r.pos;
        fn(c).exprs = fn(c).exprs.filter((e) => e.pos[0] !== pos[0]);
      },
      "no claimed type",
    ],
    [
      "non-null equality remains unsupported",
      (a) => {
        a.functions[0].body[0].e.r.lit = { a: "booleanlit", v: "true" };
      },
      "equality requires a null literal operand",
    ],
    [
      "loose equality remains unsupported",
      (a) => {
        a.functions[0].body[0].e.op = "==";
      },
      "only strict equality",
    ],
  ]) {
    const a = structuredClone(ast),
      c = structuredClone(claims);
    mutate(a, c);
    expect(name, run("--produce-stateful-source", a, c), false, reason);
  }
  const changed = structuredClone(ast);
  changed.functions[0].body[0].e.op = "!==";
  expect(
    "old evidence rejects opposite equality",
    run("--check-stateful-source", changed, claims, evidence),
    false,
  );
  expect(
    "null guard edge refinement remains a verifier limit",
    run(
      "--produce-stateful-source",
      JSON.parse(fs.readFileSync(guardAstPath)),
      JSON.parse(fs.readFileSync(guardClaimsPath)),
      undefined,
      guardFile,
    ),
    false,
    "source incoming edge obligation",
  );
  const context = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(file, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
    context,
    { timeout: 1000 },
  );
  for (const value of [null, true, false]) {
    assert.equal(context.isNull(value), value === null);
    assert.equal(context.nullFirst(value), value === null);
    assert.equal(context.isPresent(value), value !== null);
    assert.equal(context.nullNotFirst(value), value !== null);
    assert.equal(context.nullableCallback(value), value === null);
  }
  assert.equal(context.effectfulNullTest(), true);
  passed++;
  console.log(`Null predicates: ${passed} passed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
