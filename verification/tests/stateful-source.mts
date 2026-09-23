#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import {
  atom,
  binding,
  claimFrom,
  entryAt,
  expr,
  field,
  fn as functionIn,
  last,
  list,
  must,
  at as nth,
  sole,
  stmt,
  sourceType,
} from "./edits.mts";
// Exercise the source consumer using actual parser output and SKJS exports.




const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "stateful-source-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const fn =(c: SkjsClaims) => functionOf(c, fileKey, "copyTrue");
const branchAst =(a: Ast) => functionIn(a, "mergeWithLocals");
const branchClaims =(c: SkjsClaims) => functionOf(c, fileKey, "mergeWithLocals");
const refinedAst =(a: Ast) => functionIn(a, "narrowVariable");
const refinedClaims =(c: SkjsClaims) => functionOf(c, fileKey, "narrowVariable");
const parameterAst =(a: Ast) => functionIn(a, "selectParameter");
const parameterClaims =(c: SkjsClaims) => functionOf(c, fileKey, "selectParameter");
const ty =(v: string): ClaimType => ({ top: false, atoms: [{ a: "booleanlit", v }] });
/** The binding this fixture's first function copies, and the `if` a named
 * function branches on. */
const copied = (a: Ast) => sole(stmt(nth(a.functions[0].body, 0), "const"));
const branch = (f: FunctionAst) => stmt(must(f.body.find((s) => s.k === "if"), "an if"), "if");
let passed = 0;
function run(mode: string, a: Ast, c: unknown, evidence?: unknown) {
  fs.writeFileSync(path.join(tmp, "ast.json"), JSON.stringify(a));
  fs.writeFileSync(path.join(tmp, "claims.json"), JSON.stringify(c));
  if (evidence !== undefined) fs.writeFileSync(path.join(tmp, "evidence.json"), JSON.stringify(evidence));
  const args = [mode, path.join(tmp, "ast.json"), path.join(tmp, "claims.json"), fileKey, path.join(tmp, "evidence.json")];
  if (mode === "--produce-stateful-source") args.push("8");
  const r = spawnSync(verifier, args, { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
}
function expect(
  name: string,
  r: { status: number | null; stdout: string; stderr: string },
  accept: boolean,
  message = "",
) {
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
  const cases: [string, (a: Ast, c: SkjsClaims) => void, string?][] = [
    ["false claim for true initializer", (a,c) => { claimFrom(fn(c), copied(a).init.pos[0]).type = ty("false"); }, "evidence search failed"],
    ["source annotation independently enforced", a => { copied(a).annot = sourceType(ty("false")); }, "evidence search failed"],
    ["incoming edge rejects invented refinement", (a,c) => { binding(fn(c), nth(a.functions[0].body, 1).pos[0], "x").type = ty("false"); }, "evidence search failed"],
    ["missing statement environment", (a,c) => { fn(c).envs = []; }, "missing statement environment"],
    ["missing expression claim", (a,c) => { fn(c).exprs = []; }, "no claimed type"],
    ["missing local binding", (a,c) => { fn(c).envs.forEach((e) => e.vars = e.vars.filter((v) => v.name !== "x")); }, "missing claimed binding"],
    ["duplicate claim", (a,c) => { fn(c).exprs.push(clone(must(fn(c).exprs[0], "a claim"))); }, "duplicate source claim sites or bindings"],
    ["malformed singleton", (a,c) => { must(fn(c).exprs[0], "a claim").type = ty("maybe"); }, "boolean literal must be exactly"],
    ["malformed source literal", a => { atom(expr(copied(a).init, "lit").lit, "booleanlit").v = "maybe"; }, "boolean literal must be exactly"],
    ["return signature mismatch", (a,c) => { fn(c).retType = ty("true"); }, "claimed return type differs"],
    ["uninitialized source read", a => { const bound = copied(a); bound.init = { k: "id", pos: bound.init.pos, name: "x" }; }, "unbound or uninitialized"],
    ["duplicate local declaration", a => { sole(stmt(nth(a.functions[0].body, 1), "const")).name = "x"; }, "duplicate or shadowing local declaration"],
    ["duplicate file claims", (a,c) => { c.push(clone(fileOf(c, fileKey))); }, "exactly one matching claim file"],
    ["duplicate source identity", a => { a.functions[1] = clone(a.functions[0]); }, "duplicate function identity"],
    // Falling off the end is not refused, it is checked: the exit carries the
    // value a completing body produces, and `undefined` establishes nothing the
    // source can declare. Asserting on the term pins the reason, not just the
    // refusal.
    ["completing body must establish the result", a => { a.functions[0].body.pop(); }, '"term":"undef"'],
    ["unjustified merge claim", (a,c) => {
      binding(branchClaims(c), last(branchAst(a).body).pos[0], "outer").type = ty("false");
    }, "evidence search failed"],
    ["unjustified arm entry", (a,c) => {
      const entry = nth(stmt(nth(branchAst(a).body, 1), "if").then, 0).pos[0];
      binding(branchClaims(c), entry, "outer").type = ty("false");
    }, "evidence search failed"],
    ["nonboolean condition", (a,c) => {
      const condition = expr(stmt(nth(branchAst(a).body, 1), "if").cond, "lit");
      condition.lit = { a: "null" };
      claimFrom(branchClaims(c), condition.pos[0]).type = { top: false, atoms: [{ a: "null" }] };
    }, "evidence search failed"],
    ["branch local cannot escape", a => { expr(stmt(last(branchAst(a).body), "return").e, "id").name = "local"; }, "unbound or uninitialized"],
    ["active-name shadowing gate", a => { sole(stmt(nth(stmt(nth(branchAst(a).body, 1), "if").then, 0), "const")).name = "outer"; }, "duplicate or shadowing"],
    ["opposite refinement on true edge", (a,c) => {
      const arm = nth(branch(refinedAst(a)).then, 0);
      binding(refinedClaims(c), arm.pos[0], "condition").type = ty("false");
    }, "evidence search failed"],
    ["opposite refinement on false edge", (a,c) => {
      const arm = nth(must(branch(refinedAst(a)).else_, "an else arm"), 0);
      binding(refinedClaims(c), arm.pos[0], "condition").type = ty("true");
    }, "evidence search failed"],
    ["unrelated binding cannot be refined", (a,c) => {
      const arm = nth(branch(refinedAst(a)).then, 0);
      binding(refinedClaims(c), arm.pos[0], "other").type = ty("true");
    }, "evidence search failed"],
    ["narrow claimed parameter signature", (a,c) => { must(parameterClaims(c).params[1], "a parameter").type = ty("true"); }, "claimed parameter type differs"],
    ["parameter claim count", (a,c) => { parameterClaims(c).params.pop(); }, "parameter claim count mismatch"],
    ["parameter claim order", (a,c) => { parameterClaims(c).params.reverse(); }, "parameter claim name or order mismatch"],
    ["duplicate source parameter", a => { must(parameterAst(a).params[1], "a parameter").name = "first"; }, "duplicate source parameter name"],
    ["unjustified entry refinement", (a,c) => {
      const initial = nth(parameterAst(a).body, 0).pos[0];
      binding(parameterClaims(c), initial, "second").type = ty("true");
    }, "evidence search failed"],
    ["missing parameter entry binding", (a,c) => {
      const env = entryAt(parameterClaims(c), nth(parameterAst(a).body, 0).pos[0]);
      env.vars = env.vars.filter((v) => v.name !== "second");
    }, "missing claimed binding"],
    ["shifted function identity", (a,c) => { fn(c).namePos[0]++; }, "claim function identity is absent from source"],
    ["missing function claims", (a,c) => { fileOf(c, fileKey).functions.pop(); }, "function claim count mismatch"],
    ["renamed claim file", (a,c) => { fileOf(c, fileKey).file += ".other"; }, "exactly one matching claim file"],
    ["never expression claim", (a,c) => { must(fn(c).exprs[0], "a claim").type = {top:false,atoms:[]}; }, "evidence search failed"],
    ["never incoming binding", (a,c) => {
      binding(fn(c), nth(a.functions[0].body, 1).pos[0], "x").type = {top:false,atoms:[]};
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
  fileOf(reordered, fileKey).functions.reverse();
  expect("export order is irrelevant", run("--check-stateful-source", ast, reordered, evidence), true);
  const dropped = clone(evidence);
  list(field(dropped, "functions"), "the certificates").pop();
  expect("missing function certificate", run("--check-stateful-source", ast, claims, dropped), false);
  expect("unknown evidence field", run("--check-stateful-source", ast, claims, { ...evidence, trusted: true }), false);
  console.log(`Stateful source: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
