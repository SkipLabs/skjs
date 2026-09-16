#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import type { Row } from "../tools/type-graph.mts";
import { functionOf, type SkjsClaims, type SkjsFunction } from "../tools/skjs-claims.mts";
import { at as nth, atom, claimAt, claimType, expr, rows, stmt } from "./edits.mts";
import surface from "../tools/claim-text.mts";
const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "function-field-"));
try {
  const ast: Ast = JSON.parse(fs.readFileSync(astPath,"utf8"));
  const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath,"utf8"));
  const input=path.join(work,"ast"), contract=path.join(work,"claims"), evidence=path.join(work,"evidence");
  const run=(mode: string,a: Ast,c: SkjsClaims)=>{
    fs.writeFileSync(input,JSON.stringify(a)); fs.writeFileSync(contract,JSON.stringify(c));
    const args=[mode,input,contract,file,evidence];
    if(mode==="--produce-stateful-source") args.push("10");
    const r=spawnSync(verifier,args,{encoding:"utf8"});
    if(r.error||r.signal) throw r.error||Error(String(r.signal));
    return r;
  };
  for(const mode of ["--produce-stateful-source","--check-stateful-source"]) {
    const r=run(mode,ast,claims); assert.equal(r.status,0,r.stdout+r.stderr);
  }
  const fn=ast.functions[0], fc=functionOf(claims,file,fn.name);
  const assign=expr(stmt(nth(fn.body,0),"const").init,"withValue");
  const combined=claimType(claimAt(fc,assign.pos));
  assert.equal(combined.atoms[0].a,"callable");
  assert(surface.roundTrips(combined),"combined call/property contract must survive report editing");
  // Supply a complete callable/object claim from text with no producer template.
  const manual = structuredClone(claims);
  const manualFn = functionOf(manual,file,fn.name);
  claimAt(manualFn,assign.pos).type = surface.parseType("((boolean) => boolean) & { value: boolean }");
  for (const mode of ["--produce-stateful-source","--check-stateful-source"]) {
    const r = run(mode,ast,manual); assert.equal(r.status,0,r.stdout+r.stderr);
  }
  claimAt(manualFn,assign.pos).type = surface.parseType("((boolean) => boolean) & { value: null }");
  assert.notEqual(run("--produce-stateful-source",ast,manual).status,0,"fresh field claims still require evidence");
  assert.equal(run("--produce-stateful-source",ast,claims).status,0);
  const table: Row[] = [["nul"], [{boolLit: {value: true}}], [{boolLit: {value: false}}], ["undef"]];
  const normalized = surface.lower(table, combined);
  const lifted = surface.lift(table, normalized.type);
  assert(surface.roundTrips(lifted), "normalized callable contract remains editable");
  assert.deepEqual(surface.lower(table, lifted), normalized);
  for(const [name,edit] of rows<[string,(a: FunctionAst,c: SkjsFunction)=>void]>([
    ["field invariant", (a,c)=>{atom(claimType(claimAt(c,assign.pos)).atoms[0],"callable").bag.fields[0].write={top:false,atoms:[{a:"null"}]};}],
    ["call signature", (a,c)=>{atom(claimType(claimAt(c,assign.pos)).atoms[0],"callable").function.result={top:false,atoms:[{a:"null"}]};}],
    ["source field annotation", (a,c)=>{const field=atom(expr(stmt(nth(a.body,0),"const").init,"withValue").bagType.atoms[0],"record").fields[0];field.read=field.write={top:false,atoms:[{a:"null"}]};}],
  ])) {
    const a=structuredClone(ast),c=structuredClone(claims);
    edit(a.functions[0],functionOf(c,file,fn.name));
    for(const mode of ["--check-stateful-source","--produce-stateful-source"])
      assert.notEqual(run(mode,a,c).status,0,name);
  }
  const source = fs.readFileSync(file, "utf8");
  for (const [name, text] of [
    ["shadowed builtin", source.replace("callableField(seed: boolean)", "callableField(seed: boolean, Object: unknown)")],
    ["aliased target", source.replace("(next: boolean): boolean => next,", "seed,")],
    ...["call", "bind", "name", "length", "caller", "arguments", "__proto__"].map(name => [
      `special field ${name}`, source.replace("{ value: seed }", `{ value: seed, ${name}: seed }`),
    ]),
    ["accessor", source.replace("{ value: seed }", "{ get value() { return seed; } }")],
    ["extra source", source.replace("{ value: seed },", "{ value: seed }, { value: seed },")],
  ]) {
    const probe = path.join(work, "probe.ts");
    fs.writeFileSync(probe, text);
    const result = spawnSync(process.execPath, ["verification/tools/fragment-parse.mts", probe], {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    assert.notEqual(result.status, 0, name);
  }
  console.log("  callable field: creation, alias/write/call, report round trip and independent contract rejection OK");
} finally { fs.rmSync(work,{recursive:true,force:true}); }
