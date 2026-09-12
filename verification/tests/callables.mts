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

  for (const [name, edit] of [
    ["argument must fit every selected callable", (call, at) => {
      call.arg.lit.v = "false";
      at(call.arg).type = lit("false");
    }],
    ["claimed callee cannot widen a narrow domain", (call, at) => {
      const arrows = at(call.callee).type.atoms;
      assertCallableAlternatives(arrows);
      assert(arrows.some((a: any) => JSON.stringify(a.params[0]) === JSON.stringify(lit("true"))));
      for (const arrow of arrows) arrow.params[0] = {top: false, atoms: [{a: "boolean"}]};
      call.arg.lit.v = "false";
      at(call.arg).type = lit("false");
    }],
    ["callee claim cannot discard the restrictive alternative", (call, at) => {
      const type = at(call.callee).type;
      assertCallableAlternatives(type.atoms);
      type.atoms = type.atoms.filter((a: any) => a.params[0].atoms.some((p: any) => p.a === "boolean"));
      assert.equal(type.atoms.length, 1);
      call.arg.lit.v = "false";
      at(call.arg).type = lit("false");
    }],
    ["shared-domain result must retain both alternatives", (call, at) => {
      at(call).type = lit("true");
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a = clone(ast), c = clone(claims);
    const f = a.functions.find((f: any) => f.name === "sharedCallableDomain");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "sharedCallableDomain");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    edit(f.body[0].init.body.body.e, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of [
    ["false branch cannot borrow the true-only domain", (b, at) => {
      assert.deepEqual(at(b.then.arg).type, lit("true"));
      assert.deepEqual(at(b.else_.arg).type, lit("false"));
      b.else_.callee.name = "narrow";
      at(b.else_.callee).type = clone(at(b.then.callee).type);
      at(b.else_).type = clone(at(b.then).type);
    }],
    ["branch argument claim must match the tested value", (b, at) => {
      at(b.else_.arg).type = lit("true");
    }],
    ["branch result must match its own callee", (b, at) => {
      assert.deepEqual(at(b.then).type, lit("false"));
      at(b.then).type = lit("true");
    }],
    ["joined call result cannot retain one branch only", (b, at) => {
      at(b).type = lit("true");
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a = clone(ast), c = clone(claims);
    const f = a.functions.find((f: any) => f.name === "branchLocalCallableDomains");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "branchLocalCallableDomains");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    edit(f.body[0].init.body, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of [
    ["argument write must satisfy the callee domain", (body, at) => {
      at(body[2].init.callee).type.atoms[0].params[0] = lit("true");
    }],
    ["argument write must satisfy the cell invariant", (body, at) => {
      const arg = body[2].init.arg;
      arg.rhs.lit = {a: "null"};
      at(arg.rhs).type = {top: false, atoms: [{a: "null"}]};
      at(arg).type = clone(at(arg.rhs).type);
    }],
    ["assignment argument must return its RHS", (body, at) => {
      at(body[2].init.arg).type = {top: false, atoms: [{a: "null"}]};
    }],
    ["captured read cannot invent a singleton", (body, at) => {
      at(body[1].init.body).type = lit("true");
    }],
  ] as [string, (...xs: any[]) => any][]) {
    const a = clone(ast), c = clone(claims);
    const f = a.functions.find((f: any) => f.name === "callableArgumentWrite");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "callableArgumentWrite");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    edit(f.body, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  // The assignment returns false, although the original exporter claims only
  // Boolean. An explicit refinement supports a false-only view of the callee.
  {
    const c = clone(claims);
    const f = ast.functions.find((f: any) => f.name === "callableArgumentWrite");
    const fc = c.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "callableArgumentWrite");
    const at = (e: any) => fc.exprs.find((q: any) => q.pos[0] === e.pos[0] && q.pos[1] === e.pos[1]);
    const call = f.body[2].init;
    assert.deepEqual(at(call.arg).type, {top: false, atoms: [{a: "boolean"}]});
    at(call.arg).type = lit("false");
    at(call.callee).type.atoms[0].params[0] = lit("false");
    expect("explicit assignment refinement satisfies false-only view", run("--produce-stateful-source", ast, c), true);
    const refined = JSON.parse(fs.readFileSync(path.join(tmp, "evidence"), "utf8"));
    expect("independent refined assignment consumer", run("--check-stateful-source", ast, c, refined), true);
    expect("original evidence cannot replace refined assignment proof", run("--check-stateful-source", ast, c, evidence), false);
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
