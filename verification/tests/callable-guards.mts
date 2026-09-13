#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "callable-guards-"));
try {
  const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims");
  const evidence = path.join(work, "evidence");
  const run = (mode: string, a: any, c: any) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = run(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  for (const [name, edit] of [
    ["opposite polarity cannot justify invocation", (f: any) => { f.body[0].cond.equal = false; }],
    ["another same-typed input cannot justify refinement", (f: any) => { f.body[0].cond.e.name = "other"; }],
  ] as [string, (f: any) => void][]) {
    const changed = structuredClone(ast);
    edit(changed.functions.find((f: any) => f.name === "guardedShape"));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(run(mode, changed, claims).status, 0, name);
  }
  const forged = structuredClone(claims);
  const fn = ast.functions.find((f: any) => f.name === "guardedShape");
  const pos = fn.body[0].then[0].e.callee.pos;
  const fc = forged.find((b: any) => b.file === file).functions.find((f: any) => f.name === fn.name);
  const call = fc.exprs.find((e: any) => e.pos[0] === pos[0] && e.pos[1] === pos[1]);
  call.type.atoms[0].result = {top: false, atoms: [{a: "booleanlit", v: "true"}]};
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
    assert.notEqual(run(mode, ast, forged).status, 0, "shape cannot invent a more precise callable result");
  console.log("  function guards: both polarities, captured refinement, value test, and forged evidence rejection OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
