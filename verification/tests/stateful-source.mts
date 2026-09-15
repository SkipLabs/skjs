#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
// Exercise the source consumer using actual parser output and SKJS exports.




const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "stateful-source-"));
const clone =(x: any) => JSON.parse(JSON.stringify(x));
const fn =(c: any) => c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "copyTrue");
const branchAst =(a: any) => a.functions.find((f: any) => f.name === "mergeWithLocals");
const branchClaims =(c: any) => c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "mergeWithLocals");
const refinedAst =(a: any) => a.functions.find((f: any) => f.name === "narrowVariable");
const refinedClaims =(c: any) => c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "narrowVariable");
const parameterAst =(a: any) => a.functions.find((f: any) => f.name === "selectParameter");
const parameterClaims =(c: any) => c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "selectParameter");
const ty =(v: any) => ({ top: false, atoms: [{ a: "booleanlit", v }] });
let passed = 0;
function run(mode: string, a: any, c: any, evidence?: any) {
  fs.writeFileSync(path.join(tmp, "ast.json"), JSON.stringify(a));
  fs.writeFileSync(path.join(tmp, "claims.json"), JSON.stringify(c));
  if (evidence !== undefined) fs.writeFileSync(path.join(tmp, "evidence.json"), JSON.stringify(evidence));
  const args = [mode, path.join(tmp, "ast.json"), path.join(tmp, "claims.json"), fileKey, path.join(tmp, "evidence.json")];
  if (mode === "--produce-stateful-source") args.push("8");
  const r = spawnSync(verifier, args, { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
}
function expect(name: string, r: any, accept: any, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || !output.includes(message)) {
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  }
  passed++;
  console.log(`  ${name}: OK`);
}
try {
  expect("produce real source certificates", run("--produce-stateful-source", ast, claims), true);
  const evidence = JSON.parse(fs.readFileSync(path.join(tmp, "evidence.json"), "utf8"));
  expect("independent source consumer", run("--check-stateful-source", ast, claims, evidence), true);
  const cases: [string, (a: any, c?: any) => void, string?][] = [
    ["false claim for true initializer", (a,c) => { fn(c).exprs.find((e: any) => e.pos[0] === a.functions[0].body[0].init.pos[0]).type = ty("false"); }, "evidence search failed"],
    ["source annotation independently enforced", a => { a.functions[0].body[0].annot = ty("false"); }, "evidence search failed"],
    ["incoming edge rejects invented refinement", (a,c) => { fn(c).envs.find((e: any) => e.pos[0] === a.functions[0].body[1].pos[0]).vars.find((v: any) => v.name === "x").type = ty("false"); }, "evidence search failed"],
    ["missing statement environment", (a,c) => { fn(c).envs = []; }, "missing statement environment"],
    ["missing expression claim", (a,c) => { fn(c).exprs = []; }, "no claimed type"],
    ["missing local binding", (a,c) => { fn(c).envs.forEach((e: any) => e.vars = e.vars.filter((v: any) => v.name !== "x")); }, "missing claimed binding"],
    ["duplicate claim", (a,c) => { fn(c).exprs.push(clone(fn(c).exprs[0])); }, "duplicate source claim sites or bindings"],
    ["malformed singleton", (a,c) => { fn(c).exprs[0].type = ty("maybe"); }, "boolean literal must be exactly"],
    ["malformed source literal", a => { a.functions[0].body[0].init.lit.v = "maybe"; }, "boolean literal must be exactly"],
    ["return signature mismatch", (a,c) => { fn(c).retType = ty("true"); }, "claimed return type differs"],
    ["uninitialized source read", a => { a.functions[0].body[0].init = { k: "id", pos: a.functions[0].body[0].init.pos, name: "x" }; }, "unbound or uninitialized"],
    ["duplicate local declaration", a => { a.functions[0].body[1].name = "x"; }, "duplicate or shadowing local declaration"],
    ["duplicate file claims", (a,c) => { c.push(clone(c.find((f: any) => f.file === fileKey))); }, "exactly one matching claim file"],
    ["duplicate source identity", a => { a.functions[1] = clone(a.functions[0]); }, "duplicate function identity"],
    // Falling off the end is not refused, it is checked: the exit carries the
    // value a completing body produces, and `undefined` establishes nothing the
    // source can declare. Asserting on the term pins the reason, not just the
    // refusal.
    ["completing body must establish the result", a => { a.functions[0].body.pop(); }, '"term":"undef"'],
    ["unjustified merge claim", (a,c) => {
      const end = branchAst(a).body.at(-1).pos[0];
      branchClaims(c).envs.find((e: any) => e.pos[0] === end).vars.find((v: any) => v.name === "outer").type = ty("false");
    }, "evidence search failed"],
    ["unjustified arm entry", (a,c) => {
      const entry = branchAst(a).body[1].then[0].pos[0];
      branchClaims(c).envs.find((e: any) => e.pos[0] === entry).vars.find((v: any) => v.name === "outer").type = ty("false");
    }, "evidence search failed"],
    ["nonboolean condition", (a,c) => {
      const condition = branchAst(a).body[1].cond;
      condition.lit = { a: "null" };
      branchClaims(c).exprs.find((e: any) => e.pos[0] === condition.pos[0]).type = { top: false, atoms: [{ a: "null" }] };
    }, "evidence search failed"],
    ["branch local cannot escape", a => { branchAst(a).body.at(-1).e.name = "local"; }, "unbound or uninitialized"],
    ["active-name shadowing gate", a => { branchAst(a).body[1].then[0].name = "outer"; }, "duplicate or shadowing"],
    ["opposite refinement on true edge", (a,c) => {
      const arm = refinedAst(a).body.find((s: any) => s.k === "if").then[0];
      refinedClaims(c).envs.find((e: any) => e.pos[0] === arm.pos[0]).vars.find((v: any) => v.name === "condition").type = ty("false");
    }, "evidence search failed"],
    ["opposite refinement on false edge", (a,c) => {
      const arm = refinedAst(a).body.find((s: any) => s.k === "if").else_[0];
      refinedClaims(c).envs.find((e: any) => e.pos[0] === arm.pos[0]).vars.find((v: any) => v.name === "condition").type = ty("true");
    }, "evidence search failed"],
    ["unrelated binding cannot be refined", (a,c) => {
      const arm = refinedAst(a).body.find((s: any) => s.k === "if").then[0];
      refinedClaims(c).envs.find((e: any) => e.pos[0] === arm.pos[0]).vars.find((v: any) => v.name === "other").type = ty("true");
    }, "evidence search failed"],
    ["narrow claimed parameter signature", (a,c) => { parameterClaims(c).params[1].type = ty("true"); }, "claimed parameter type differs"],
    ["parameter claim count", (a,c) => { parameterClaims(c).params.pop(); }, "parameter claim count mismatch"],
    ["parameter claim order", (a,c) => { parameterClaims(c).params.reverse(); }, "parameter claim name or order mismatch"],
    ["duplicate source parameter", a => { parameterAst(a).params[1].name = "first"; }, "duplicate source parameter name"],
    ["unjustified entry refinement", (a,c) => {
      const initial = parameterAst(a).body[0].pos[0];
      parameterClaims(c).envs.find((e: any) => e.pos[0] === initial).vars.find((v: any) => v.name === "second").type = ty("true");
    }, "evidence search failed"],
    ["missing parameter entry binding", (a,c) => {
      const initial = parameterAst(a).body[0].pos[0];
      const env = parameterClaims(c).envs.find((e: any) => e.pos[0] === initial);
      env.vars = env.vars.filter((v: any) => v.name !== "second");
    }, "missing claimed binding"],
    ["shifted function identity", (a,c) => { fn(c).namePos[0]++; }, "claim function identity is absent from source"],
    ["missing function claims", (a,c) => { c.find((f: any) => f.file === fileKey).functions.pop(); }, "function claim count mismatch"],
    ["renamed claim file", (a,c) => { c.find((f: any) => f.file === fileKey).file += ".other"; }, "exactly one matching claim file"],
    ["never expression claim", (a,c) => { fn(c).exprs[0].type = {top:false,atoms:[]}; }, "evidence search failed"],
    ["never incoming binding", (a,c) => {
      fn(c).envs.find((e: any) => e.pos[0] === a.functions[0].body[1].pos[0]).vars.find((v: any) => v.name === "x").type = {top:false,atoms:[]};
    }, "evidence search failed"],
    ["AST identity mismatch", a => { a.file = "other.ts"; }, "AST file key mismatch"],
  ];
  for (const [name, alter, message] of cases) {
    const a = clone(ast), c = clone(claims);
    alter(a,c);
    expect(name, run("--produce-stateful-source", a,c), false, message);
    expect(`${name} (consumer)`, run("--check-stateful-source", a,c,evidence), false);
  }
  const reordered = clone(claims);
  reordered.find((f: any) => f.file === fileKey).functions.reverse();
  expect("export order is irrelevant", run("--check-stateful-source", ast, reordered, evidence), true);
  const dropped = clone(evidence);
  dropped.functions.pop();
  expect("missing function certificate", run("--check-stateful-source", ast, claims, dropped), false);
  expect("unknown evidence field", run("--check-stateful-source", ast, claims, { ...evidence, trusted: true }), false);
  console.log(`Stateful source: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
