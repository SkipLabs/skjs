#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import surface from "../tools/claim-types.mts";

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callables-"));
const clone = (x: any) => structuredClone(x);
const lit = (v: string) => ({top: false, atoms: [{a: "booleanlit", v}]});
let passed = 0;

function run(mode: string, a: any, c: any, evidence?: any) {
  fs.writeFileSync(path.join(tmp, "ast"), JSON.stringify(a));
  fs.writeFileSync(path.join(tmp, "claims"), JSON.stringify(c));
  if (evidence) fs.writeFileSync(path.join(tmp, "evidence"), JSON.stringify(evidence));
  const args = [mode, path.join(tmp, "ast"), path.join(tmp, "claims"), fileKey, path.join(tmp, "evidence")];
  if (mode === "--produce-stateful-source") args.push("10");
  const result = spawnSync(verifier, args, {encoding: "utf8"});
  if (result.error || result.signal) throw result.error || Error(String(result.signal));
  return result;
}

function expect(name: string, result: {status: number | null; stdout: string; stderr: string}, accept: boolean) {
  assert.equal(result.status === 0, accept, `${name}: ${result.stdout}${result.stderr}`);
  passed++;
  console.log(`  ${name}: OK`);
}

try {
  expect("produce callable certificates", run("--produce-stateful-source", ast, claims), true);
  const evidence = JSON.parse(fs.readFileSync(path.join(tmp, "evidence"), "utf8"));
  expect("independent callable consumer", run("--check-stateful-source", ast, claims, evidence), true);

  for(const [name,edit] of [
    ["coalesced callable cannot discard fallback",(b,at)=>{
      const t=at(b.callee).type;
      const arrows=t.atoms.filter((a: any)=>a.a==="function");
      assertCallableAlternatives(arrows);
      t.atoms=[arrows.find((a: any)=>a.result.atoms.some((r: any)=>r.a==="booleanlit"&&r.v==="true"))];
    }],
    ["coalesced call result cannot narrow",(b,at)=>{at(b).type=lit("true");}],
    ["nullish original cannot be its own fallback",b=>{b.callee.right.name="f";}],
    ["null fallback cannot supply a callable",(b,at)=>{
      const r=b.callee.right;at(r).type={top:false,atoms:[{a:"null"}]};
      b.callee.right={k:"lit",pos:r.pos,lit:{a:"null"}};
    }],
    ["coalesced callable checks the argument",(b,at)=>{
      at(b.arg).type=lit("true");b.arg={k:"lit",pos:b.arg.pos,lit:{a:"booleanlit",v:"true"}};
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims);
    const f=a.functions.find((f: any)=>f.name==="coalescedCallable");
    const fc=c.find((f: any)=>f.file===fileKey).functions.find((f: any)=>f.name==="coalescedCallable");
    const at=(e: any)=>fc.exprs.find((q: any)=>q.pos[0]===e.pos[0]&&q.pos[1]===e.pos[1]);
    edit(f.body[0].init.body,at);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }

  for (const functionName of ["andGuardedCallable", "orGuardedCallable"]) {
    for (const [name, edit] of [
      ["reversed guard cannot justify the call", (b, at) => {
        b.l.op = b.l.op === "===" ? "!==" : "===";
      }],
      ["opposite short-circuit operator cannot justify the call", (b, at) => {
        b.op = b.op === "&&" ? "||" : "&&";
      }],
      ["result must include the skipped branch", (b, at) => {
        const called = at(b.r).type;
        assert.deepEqual(called, lit(functionName === "andGuardedCallable" ? "true" : "false"));
        at(b).type = clone(called);
      }],
    ] as [string, (...xs: any[]) => any][]) {
      const a = clone(ast), c = clone(claims);
      const f = a.functions.find((f: any) => f.name === functionName);
      const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === functionName);
      const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
      edit(f.body[0].init.body, at);
      expect(`${functionName}: ${name}`, run("--produce-stateful-source", a, c), false);
      expect(`${functionName}: ${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
    }
  }

  for (const [name, edit] of [
    ["reversed guard cannot justify an escaping capture", (branch, at) => {
      branch.cond.op = "!==";
    }],
    ["escaping capture must retain both alternatives", (branch, at) => {
      const callee = at(branch.else_[0].e.body.callee).type;
      assertCallableAlternatives(callee.atoms);
      callee.atoms = [callee.atoms[0]];
    }],
    ["returned closure signature cannot narrow", (branch, at) => {
      at(branch.else_[0].e).type.atoms[0].result = lit("true");
    }],
    ["later invocation result cannot narrow", (branch, at) => {
      at(branch.else_[0].e.body).type = lit("true");
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a = clone(ast), c = clone(claims);
    const f = a.functions.find((f: any) => f.name === "capturedGuardedCallable");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "capturedGuardedCallable");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    edit(f.body[0], at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of [
    ["alias selection must respect the guard", (b, at, fc) => {
      b.init.cond.op = "!==";
    }],
    ["selected alias cannot make the original callable", (b, at, fc) => {
      b.body.init.body.callee.name = "f";
    }],
    ["alias initializer must retain the fallback", (b, at, fc) => {
      const type = at(b.init).type;
      assertCallableAlternatives(type.atoms);
      type.atoms = [type.atoms[0]];
    }],
    ["joined alias entry cannot discard an alternative", (b, at, fc) => {
      const entry = fc.envs.find((e: any) => e.pos[0] === b.body.pos[0]);
      const type = entry.vars.find((v: any) => v.name === "selected").type;
      assertCallableAlternatives(type.atoms);
      type.atoms = [type.atoms[0]];
    }],
    ["nested alias call result cannot narrow", (b, at, fc) => {
      at(b.body.init.body).type = lit("true");
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a = clone(ast), c = clone(claims);
    const f = a.functions.find((f: any) => f.name === "aliasedCallableSelection");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "aliasedCallableSelection");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    edit(f.body[0].init.body, at, fc);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  const types: any[] = [];
  for (const file of claims) for (const f of file.functions) {
    types.push(f.retType, ...f.params.map((p: any) => p.type), ...f.exprs.map((e: any) => e.type));
    for (const env of f.envs) types.push(...env.vars.map((v: any) => v.type));
  }
  assert(types.length > 0);
  for (const type of types) {
    if (type && !type.unsupported && surface.printType(type).printable)
      assert.deepEqual(surface.parseType(surface.printType(type).text, type), type);
  }
  passed++;
  console.log("  callable claim types survive report round trips: OK");

  const report = path.join(tmp, "callables.annotated.ts");
  const annotated = spawnSync(process.execPath, [
    path.resolve(import.meta.dirname, "../tools/annotate-source.mts"), fileKey,
    "--claims", claimsPath, "--verify", verifier, "--out", report,
  ], {encoding: "utf8"});
  if (annotated.error || annotated.signal) throw annotated.error || Error(String(annotated.signal));
  expect("independently verified callable report", annotated, true);
  const manifest = JSON.parse(fs.readFileSync(report + ".json", "utf8"));
  assert.equal(manifest.results.length, ast.functions.length);
  assert(manifest.results.every((r: any) => r.status === "verified" && r.certificateSha256));
  console.log(`Callables: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}

function assertCallableAlternatives(arrows: any[]) {
  if(arrows.length!==2 || !["true","false"].every(v=>arrows.some(a=>
    a.result.atoms.length===1 && a.result.atoms[0].a==="booleanlit" && a.result.atoms[0].v===v)))
    throw Error("coalesced fixture must export both distinct callable results");
}
