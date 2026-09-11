#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
// Negated tests must reverse refinements without trusting them or duplicating effects.






const [
  astPath,
  claimsPath,
  file,
  verifier,
  exitAstPath,
  exitClaimsPath,
  exitFile,
  singletonAstPath,
  singletonClaimsPath,
  singletonFile,
] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(os.tmpdir() + "/negation-");
const firstClaim = (c) =>
  c
    .find((f) => f.file === file)
    .functions.find((f) => f.name === "negatedBranch");
const singleton = (v) => ({
  top: false,
  atoms: [{ a: "booleanlit", v: String(v) }],
});
let passed = 0;
function run(mode, a, c, evidence?, key = file) {
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
    "negation source production",
    run("--produce-stateful-source", ast, claims),
    true,
  );
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "negation independent consumption",
    run("--check-stateful-source", ast, claims, evidence),
    true,
  );
  const exported = spawnSync(
    verifier,
    ["--export-source-claims", astPath, claimsPath, file],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exported.status, 0, exported.stderr);
  expect(
    "negation normalized claim production",
    run("--produce-source-claims", ast, JSON.parse(exported.stdout).claims),
    true,
  );
  const normalizedEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json", "utf8"),
  );
  expect(
    "negation normalized claim consumption",
    run(
      "--check-source-claims",
      ast,
      JSON.parse(exported.stdout).claims,
      normalizedEvidence,
    ),
    true,
  );
  for (const [name, mutate, reason] of [
    [
      "negation operand claim required",
      (a, c) => {
        const pos = a.functions[0].body[0].cond.e.pos;
        firstClaim(c).exprs = firstClaim(c).exprs.filter(
          (e) => e.pos[0] !== pos[0],
        );
      },
      "no claimed type",
    ],
    [
      "negation result cannot be invented",
      (a, c) => {
        const pos = a.functions[0].body[0].cond.pos;
        firstClaim(c).exprs.find((e) => e.pos[0] === pos[0]).type =
          singleton(true);
      },
      "evidence search failed",
    ],
    [
      "reversed branch cannot invent true",
      (a, c) => {
        const start = a.functions[0].body[0].then[0].pos[0];
        firstClaim(c)
          .envs.find((e) => e.pos[0] === start)
          .vars.find((v) => v.name === "flag").type = singleton(true);
      },
      "evidence search failed",
    ],
    [
      "negation requires Boolean operand",
      (a, c) => {
        const operand = a.functions[0].body[0].cond.e;
        a.functions[0].body[0].cond.e = {
          k: "lit",
          pos: operand.pos,
          lit: { a: "null" },
        };
        firstClaim(c).exprs.find((e) => e.pos[0] === operand.pos[0]).type = {
          top: false,
          atoms: [{ a: "null" }],
        };
      },
      "evidence search failed",
    ],
  ] as [string, (a: any, c: any) => void, string][]) {
    const a = structuredClone(ast),
      c = structuredClone(claims);
    mutate(a, c);
    expect(name, run("--produce-stateful-source", a, c), false, reason);
  }
  const changed = structuredClone(ast);
  changed.functions[0].body[0].cond = {
    ...changed.functions[0].body[0].cond.e,
    pos: changed.functions[0].body[0].cond.pos,
  };
  expect(
    "old evidence rejects changed polarity",
    run("--check-stateful-source", changed, claims, evidence),
    false,
  );
  const exitAst = JSON.parse(fs.readFileSync(exitAstPath, "utf8"));
  const exitClaims = JSON.parse(fs.readFileSync(exitClaimsPath, "utf8"));
  const exitFn = exitClaims.find((f) => f.file === exitFile).functions[0];
  assert.equal(exitFn.collection.completion, "aborted");
  assert.equal(exitFn.collection.mode, "normal");
  expect(
    "broad loop exit claim loses the branch refinement at the local boundary",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
  );
  const ret = exitAst.functions[0].body.at(-1);
  const binding = exitFn.envs
    .find((e) => e.pos[0] === ret.pos[0])
    .vars.find((v) => v.name === "flag");
  const expression = exitFn.exprs.find((e) => e.pos[0] === ret.e.pos[0]);
  binding.type = singleton(true);
  expression.type = singleton(true);
  expect(
    "repaired loop exit independently provable",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    true,
  );
  const repairedEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "independent consumer accepts repaired loop",
    run(
      "--check-stateful-source",
      exitAst,
      exitClaims,
      repairedEvidence,
      exitFile,
    ),
    true,
  );
  binding.type = singleton(false);
  expect(
    "wrong loop exit refinement rejected",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
    "evidence search failed",
  );
  const singletonAst = JSON.parse(fs.readFileSync(singletonAstPath, "utf8"));
  const singletonClaims = JSON.parse(fs.readFileSync(singletonClaimsPath, "utf8"));
  const singletonFn = singletonClaims.find((f) => f.file === singletonFile)
    .functions[0];
  assert.equal(singletonFn.collection.completion, "aborted");
  assert.equal(singletonFn.collection.mode, "normal");
  expect(
    "SKJS singleton negation claim too broad",
    run(
      "--produce-stateful-source",
      singletonAst,
      singletonClaims,
      undefined,
      singletonFile,
    ),
    false,
    "evidence search failed",
  );
  const negated = singletonFn.exprs.find(
    (e) => e.pos[0] === singletonAst.functions[0].body[0].e.pos[0],
  );
  negated.type = singleton(false);
  expect(
    "singleton negation repaired by one expression claim",
    run(
      "--produce-stateful-source",
      singletonAst,
      singletonClaims,
      undefined,
      singletonFile,
    ),
    true,
  );
  const singletonEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "singleton repair independently consumed",
    run(
      "--check-stateful-source",
      singletonAst,
      singletonClaims,
      singletonEvidence,
      singletonFile,
    ),
    true,
  );
  negated.type = singleton(true);
  expect(
    "wrong singleton negation rejected",
    run(
      "--produce-stateful-source",
      singletonAst,
      singletonClaims,
      undefined,
      singletonFile,
    ),
    false,
    "evidence search failed",
  );
  const context = vm.createContext({});
  vm.runInContext(
    stripTypes(
      [file, exitFile, singletonFile]
        .map((f) => fs.readFileSync(f, "utf8"))
        .join("\n"),
    ),
    context,
    { timeout: 1000 },
  );
  vm.runInContext(
    "if (!negatedCall() || !negatedLoop()) throw Error('effects');",
    context,
    { timeout: 1000 },
  );
  for (const flag of [true, false]) {
    assert.equal(context.negatedBranch(flag), true);
    assert.equal(context.doubleNegatedBranch(flag), false);
    assert.equal(context.negatedClosure(flag), true);
    assert.equal(context.negatedVariableLoop(flag), true);
  }
  assert.equal(context.negateSingleton(true), false);
  assert.equal(context.singletonClosure(), false);
  assert.equal(context.effectfulSingletonCondition(), false);
  passed++;
  console.log(`Negation: ${passed} passed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
