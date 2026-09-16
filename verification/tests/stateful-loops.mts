import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { at, atom, binding, claimAt, expr, field, fn, list, record, rows, stmt } from "./edits.mts";
const __dirname = path.dirname(import.meta.filename);
/** The `while` a named function of this fixture loops with. */
const loop=(a: Ast,name: string)=>{
  const found=fn(a,name).body.find((s)=>s.k==="while");
  if(!found||found.k!=="while")throw Error(`${name} has no loop`);
  return found;
};
const [astPath,claimsPath,file,verifier]=process.argv.slice(2);
const ast: Ast=JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims=JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"while-source-"));
const clone=structuredClone;
const cf=(c: SkjsClaims,name: string)=>functionOf(c,file,name);
const ap=path.join(tmp,"ast.json"),cp=path.join(tmp,"claims.json"),ep=path.join(tmp,"evidence.json");
let passed=0;
const test=(name: string,f: () => void)=>{f();passed++;console.log(`  ${name}: OK`);};
const exec=(exe: string,args: string[])=>{const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;};
const run=(mode: string,a: Ast,c: SkjsClaims,e?: unknown)=>{fs.writeFileSync(ap,JSON.stringify(a));fs.writeFileSync(cp,JSON.stringify(c));if(e)fs.writeFileSync(ep,JSON.stringify(e));return exec(verifier,[mode,ap,cp,file,ep,...(mode.startsWith("--produce")?["10"]:[])]);};
try {
  test("real SKJS loop claims produce evidence",()=>{const r=run("--produce-stateful-source",ast,claims);assert.equal(r.status,0,r.stderr);});
  const evidence=JSON.parse(fs.readFileSync(ep, "utf8"));
  test("independent loop consumer",()=>assert.equal(run("--check-stateful-source",ast,claims,evidence).status,0));
  for(const [name,edit] of rows<[string, (a: Ast, c: SkjsClaims) => void]>([
    ["missing loop-head invariant",(a,c)=>{const p=loop(a,"oneWrite").pos[0];cf(c,"oneWrite").envs=cf(c,"oneWrite").envs.filter((e) =>e.pos[0]!==p);}],
    ["unjustified loop-head narrowing",(a,c)=>{const p=loop(a,"zeroTrips").pos[0];binding(cf(c,"zeroTrips"),p,"flag").type={top:false,atoms:[{a:"booleanlit",v:"true"}]};}],
    ["missing repeated condition claim",(a,c)=>{const p=loop(a,"oneWrite").cond.pos;cf(c,"oneWrite").exprs=cf(c,"oneWrite").exprs.filter((e) =>JSON.stringify(e.pos)!==JSON.stringify(p));}],
    ["body local cannot escape the loop",a=>{
      expr(expr(stmt(at(fn(a,"oneWrite").body,3),"return").e,"read").e,"id").name="alias";}],
    ["nonboolean condition",a=>{const head=loop(a,"zeroTrips");head.cond={k:"lit",pos:head.cond.pos,lit:{a:"null"}};}],
    ["missing exit return",a=>{fn(a,"zeroTrips").body.pop();}]
  ]))test(name,()=>{const a=clone(ast),c=clone(claims);edit(a,c);assert.notEqual(run("--produce-stateful-source",a,c).status,0);assert.notEqual(run("--check-stateful-source",a,c,evidence).status,0);});
  test("back-edge evidence cannot be omitted",()=>{
    const e=clone(evidence),i=ast.functions.findIndex((f) =>f.name==="oneWrite");
    const back=record(field(e,"functions",i,"certificate",4),"the loop head's node");
    assert.equal(list(field(back,"expression","node","claim","context"),"its context").length,5);
    back.edges=[];
    assert.notEqual(run("--check-stateful-source",ast,claims,e).status,0);});
  test("changed loop body cannot reuse old evidence",()=>{
    const a=clone(ast),c=clone(claims);
    const rhs=expr(expr(stmt(at(loop(a,"oneWrite").body,1),"effect").e,"write").rhs,"lit");
    atom(rhs.lit,"booleanlit").v="true";
    claimAt(cf(c,"oneWrite"),rhs.pos).type={top:false,atoms:[{a:"booleanlit",v:"true"}]};
    assert.notEqual(run("--check-stateful-source",a,c,evidence).status,0);
    const r=run("--produce-stateful-source",a,c);assert.equal(r.status,0,r.stderr); // A safe infinite loop is permitted.
  });
  test("sidecar conversion preserves cyclic requests",()=>{
    const out=path.join(tmp,"sidecar.json");const r=exec(process.execPath,[path.resolve(__dirname,"../tools/export-source-claims.mts"),file,"--claims",claimsPath,"--out",out,"--verifier",verifier]);assert.equal(r.status,0,r.stderr);
    fs.writeFileSync(ap,JSON.stringify(ast));fs.writeFileSync(ep,JSON.stringify(evidence));const checked=exec(verifier,["--check-source-claims",ap,out,file,ep]);assert.equal(checked.status,0,checked.stderr);
  });
  for(const [name,text] of [
    ["break outside a loop gated","break; return null;"],
    ["continue outside a loop gated","continue; return null;"],
    ["nonblock loop body gated","while (false) return null; return null;"],
    ["for remains gated","for (;;) {} return null;"],
    ["closure loop remains gated","const f: (x: null) => null = (x: null): null => { while (false) {} return null; }; return null;"]
  ])test(name,()=>{const file=path.join(tmp,"gated.ts");fs.writeFileSync(file,`function gated(): null { ${text} }`);const r=exec(process.execPath,[path.resolve(__dirname,"../tools/fragment-parse.mts"),file]);assert.notEqual(r.status,0);assert(r.stderr.startsWith("gate:"));});
  test("runtime samples agree on zero iterations, one write and nested return",()=>{
    const js=stripTypes(fs.readFileSync(file,"utf8"));
    const actual=vm.runInNewContext(js+"; JSON.stringify([zeroTrips(false),oneWrite(),nested(false),nested(true)])",{},{timeout:2000});
    assert.equal(actual,JSON.stringify([false,false,false,true]));
  });
  console.log(`Stateful loops: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
