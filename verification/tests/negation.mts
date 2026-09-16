#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import { functionOf } from "../tools/skjs-claims.mts";
import type { SkjsClaims } from "../tools/skjs-claims.mts";
import type { Ast } from "../tools/fragment.mts";
import { at, binding, claimFrom, expr, fn, only, rows, stmt } from "./edits.mts";
import type { SpawnSyncReturns } from "node:child_process";
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
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(os.tmpdir() + "/negation-");
const firstClaim = (c: SkjsClaims) => functionOf(c, file, "negatedBranch");
const singleton = (v: boolean) => ({
  top: false,
  atoms: [{ a: "booleanlit", v: String(v) }],
});
let passed = 0;
/** The `if` this fixture is about, and the test it branches on. */
const branch = (a: Ast) => stmt(at(fn(a, "negatedBranch").body, 0), "if");
const negatedTest = (a: Ast) => branch(a).cond;
function run(
  mode: string,
  a: Ast,
  c: unknown,
  evidence?: unknown,
  key = file,
) {
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
function expect(
  name: string,
  r: SpawnSyncReturns<string>,
  accept: boolean,
  reason = "",
) {
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
  for (const [name, mutate, reason] of rows<[string, (a: Ast, c: SkjsClaims) => void, string]>([
    [
      "negation operand claim required",
      (a, c) => {
        const pos = expr(negatedTest(a), "not").e.pos;
        firstClaim(c).exprs = firstClaim(c).exprs.filter(
          (e) => e.pos[0] !== pos[0],
        );
      },
      "no claimed type",
    ],
    [
      "negation result cannot be invented",
      (a, c) => {
        const pos = negatedTest(a).pos;
        claimFrom(firstClaim(c), pos[0]).type = singleton(true);
      },
      "evidence search failed",
    ],
    [
      "reversed branch cannot invent true",
      (a, c) => {
        const start = at(branch(a).then, 0).pos[0];
        binding(firstClaim(c), start, "flag").type = singleton(true);
      },
      "evidence search failed",
    ],
    [
      "negation requires Boolean operand",
      (a, c) => {
        const negation = expr(negatedTest(a), "not");
        const operand = negation.e;
        negation.e = { k: "lit", pos: operand.pos, lit: { a: "null" } };
        claimFrom(firstClaim(c), operand.pos[0]).type = {
          top: false,
          atoms: [{ a: "null" }],
        };
      },
      "evidence search failed",
    ],
  ])) {
    const a = structuredClone(ast),
      c = structuredClone(claims);
    mutate(a, c);
    expect(name, run("--produce-stateful-source", a, c), false, reason);
  }
  const changed = structuredClone(ast);
  const test = expr(negatedTest(changed), "not");
  branch(changed).cond = { ...test.e, pos: test.pos };
  expect(
    "old evidence rejects changed polarity",
    run("--check-stateful-source", changed, claims, evidence),
    false,
  );
  const exitAst: Ast = JSON.parse(fs.readFileSync(exitAstPath, "utf8"));
  const exitClaims: SkjsClaims = JSON.parse(
    fs.readFileSync(exitClaimsPath, "utf8"),
  );
  const exitFn = only(exitClaims, exitFile);
  assert.equal(exitFn.collection?.completion, "aborted");
  assert.equal(exitFn.collection?.mode, "normal");
  expect(
    "broad loop exit claim loses the branch refinement at the local boundary",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
  );
  const body = exitAst.functions[0].body;
  const ret = stmt(body[body.length - 1], "return");
  const flag = binding(exitFn, ret.pos[0], "flag");
  const expression = claimFrom(exitFn, ret.e.pos[0]);
  flag.type = singleton(true);
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
  flag.type = singleton(false);
  expect(
    "wrong loop exit refinement rejected",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
    "evidence search failed",
  );
  const singletonAst: Ast = JSON.parse(
    fs.readFileSync(singletonAstPath, "utf8"),
  );
  const singletonClaims: SkjsClaims = JSON.parse(
    fs.readFileSync(singletonClaimsPath, "utf8"),
  );
  const singletonFn = only(singletonClaims, singletonFile);
  assert.equal(singletonFn.collection?.completion, "aborted");
  assert.equal(singletonFn.collection?.mode, "normal");
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
  const negated = claimFrom(
    singletonFn,
    stmt(singletonAst.functions[0].body[0], "return").e.pos[0],
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
