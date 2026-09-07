#!/usr/bin/env node
// Exercise the source consumer using actual parser output and SKJS exports.
"use strict";
const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawnSync } = require("child_process");
const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "stateful-source-"));
const clone = x => JSON.parse(JSON.stringify(x));
const fn = c => c.find(f => f.file === fileKey).functions.find(f => f.name === "copyTrue");
const branchAst = a => a.functions.find(f => f.name === "mergeWithLocals");
const branchClaims = c => c.find(f => f.file === fileKey).functions.find(f => f.name === "mergeWithLocals");
const ty = v => ({ top: false, atoms: [{ a: "booleanlit", v }] });
let passed = 0;
function run(mode, a, c, evidence) {
  fs.writeFileSync(path.join(tmp, "ast.json"), JSON.stringify(a));
  fs.writeFileSync(path.join(tmp, "claims.json"), JSON.stringify(c));
  if (evidence !== undefined) fs.writeFileSync(path.join(tmp, "evidence.json"), JSON.stringify(evidence));
  const args = [mode, path.join(tmp, "ast.json"), path.join(tmp, "claims.json"), fileKey, path.join(tmp, "evidence.json")];
  if (mode === "--produce-stateful-source") args.push("8");
  const r = spawnSync(verifier, args, { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(r.signal);
  return r;
}
function expect(name, r, accept, message = "") {
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
  const cases = [
    ["false claim for true initializer", (a,c) => { fn(c).exprs.find(e => e.pos[0] === a.functions[0].body[0].init.pos[0]).type = ty("false"); }, "evidence search failed"],
    ["source annotation independently enforced", a => { a.functions[0].body[0].annot = ty("false"); }, "evidence search failed"],
    ["incoming edge rejects invented refinement", (a,c) => { fn(c).envs.find(e => e.pos[0] === a.functions[0].body[1].pos[0]).vars.find(v => v.name === "x").type = ty("false"); }, "evidence search failed"],
    ["missing statement environment", (a,c) => { fn(c).envs = []; }, "missing statement environment"],
    ["missing expression claim", (a,c) => { fn(c).exprs = []; }, "no claimed type"],
    ["missing local binding", (a,c) => { fn(c).envs.forEach(e => e.vars = e.vars.filter(v => v.name !== "x")); }, "missing claimed binding"],
    ["duplicate claim", (a,c) => { fn(c).exprs.push(clone(fn(c).exprs[0])); }, "duplicate statement or expression claim"],
    ["malformed singleton", (a,c) => { fn(c).exprs[0].type = ty("maybe"); }, "boolean literal must be exactly"],
    ["malformed source literal", a => { a.functions[0].body[0].init.lit.v = "maybe"; }, "boolean literal must be exactly"],
    ["return signature mismatch", (a,c) => { fn(c).retType = ty("true"); }, "claimed return type differs"],
    ["uninitialized source read", a => { a.functions[0].body[0].init = { k: "id", pos: a.functions[0].body[0].init.pos, name: "x" }; }, "unbound or uninitialized"],
    ["duplicate local declaration", a => { a.functions[0].body[1].name = "x"; }, "duplicate or shadowing local declaration"],
    ["duplicate file claims", (a,c) => { c.push(clone(c.find(f => f.file === fileKey))); }, "exactly one matching claim file"],
    ["duplicate source identity", a => { a.functions[1] = clone(a.functions[0]); }, "duplicate source function identities"],
    ["missing final return", a => { a.functions[0].body.pop(); }, "requires a return on every path"],
    ["unjustified merge claim", (a,c) => {
      const end = branchAst(a).body.at(-1).pos[0];
      branchClaims(c).envs.find(e => e.pos[0] === end).vars.find(v => v.name === "outer").type = ty("false");
    }, "evidence search failed"],
    ["unjustified arm entry", (a,c) => {
      const entry = branchAst(a).body[1].then[0].pos[0];
      branchClaims(c).envs.find(e => e.pos[0] === entry).vars.find(v => v.name === "outer").type = ty("false");
    }, "evidence search failed"],
    ["nonboolean condition", (a,c) => {
      const condition = branchAst(a).body[1].cond;
      condition.lit = { a: "null" };
      branchClaims(c).exprs.find(e => e.pos[0] === condition.pos[0]).type = { top: false, atoms: [{ a: "null" }] };
    }, "evidence search failed"],
    ["branch local cannot escape", a => { branchAst(a).body.at(-1).e.name = "local"; }, "unbound or uninitialized"],
    ["active-name shadowing gate", a => { branchAst(a).body[1].then[0].name = "outer"; }, "duplicate or shadowing"],
    ["AST identity mismatch", a => { a.file = "other.ts"; }, "AST file key mismatch"],
  ];
  for (const [name, alter, message] of cases) {
    const a = clone(ast), c = clone(claims);
    alter(a,c);
    expect(name, run("--produce-stateful-source", a,c), false, message);
    expect(`${name} (consumer)`, run("--check-stateful-source", a,c,evidence), false);
  }
  const reordered = clone(claims);
  reordered.find(f => f.file === fileKey).functions.reverse();
  expect("export order is irrelevant", run("--check-stateful-source", ast, reordered, evidence), true);
  const dropped = clone(evidence);
  dropped.functions.pop();
  expect("missing function certificate", run("--check-stateful-source", ast, claims, dropped), false);
  expect("unknown evidence field", run("--check-stateful-source", ast, claims, { ...evidence, trusted: true }), false);
  console.log(`Stateful source: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
