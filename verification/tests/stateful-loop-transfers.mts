import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
const [astPath,claimsPath,file,verifier]=process.argv.slice(2),ast=JSON.parse(fs.readFileSync(astPath, "utf8")),claims=JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"loop-transfers-")),ap=path.join(tmp,"ast.json"),cp=path.join(tmp,"claims.json"),ep=path.join(tmp,"evidence.json");
const sf=(a,n)=>a.functions.find(f=>f.name===n),cf=(c,n)=>c.find(f=>f.file===file).functions.find(f=>f.name===n);
const exec=(exe,args)=>{const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000});if(r.error||r.signal)throw r.error||Error(r.signal);return r;};
const run=(mode,a,c,e?)=>{fs.writeFileSync(ap,JSON.stringify(a));fs.writeFileSync(cp,JSON.stringify(c));if(e)fs.writeFileSync(ep,JSON.stringify(e));return exec(verifier,[mode,ap,cp,file,ep,...(mode.startsWith("--produce")?["10"]:[])]);};
let passed=0;const test=(name,f)=>{f();passed++;console.log(`  ${name}: OK`);};
try {
  test("SKJS break and continue claims produce evidence",()=>{const r=run("--produce-stateful-source",ast,claims);assert.equal(r.status,0,r.stderr);});
  const evidence=JSON.parse(fs.readFileSync(ep, "utf8"));
  test("independent transfer consumer",()=>assert.equal(run("--check-stateful-source",ast,claims,evidence).status,0));
  for(const name of ["stopAfterWrite","continueAfterWrite"]) {
    test(`${name}: transfer environment required`,()=>{
      const c=structuredClone(claims),p=sf(ast,name).body[2].body[2].pos[0];cf(c,name).envs=cf(c,name).envs.filter(e=>e.pos[0]!==p);
      assert.notEqual(run("--produce-stateful-source",ast,c).status,0);assert.notEqual(run("--check-stateful-source",ast,c,evidence).status,0);
    });
    test(`${name}: outgoing transfer evidence required`,()=>{
      const e=structuredClone(evidence),i=ast.functions.findIndex(f=>f.name===name);
      const node=e.functions[i].certificate.find(n=>n.expression.node.rule==="nul"&&n.expression.node.claim.context.length===3);assert(node);assert(node.edges.length);node.edges=[];
      assert.notEqual(run("--check-stateful-source",ast,claims,e).status,0);
    });
  }
  test("break must justify the exit environment",()=>{
    const c=structuredClone(claims),p=sf(ast,"nestedBreak").body[0].body[1].pos[0];cf(c,"nestedBreak").envs.find(e=>e.pos[0]===p).vars.find(v=>v.name==="flag").type={top:false,atoms:[{a:"booleanlit",v:"false"}]};
    assert.notEqual(run("--produce-stateful-source",ast,c).status,0);assert.notEqual(run("--check-stateful-source",ast,c,evidence).status,0);
  });
  test("loop body locals cannot escape break",()=>{const a=structuredClone(ast);sf(a,"stopAfterWrite").body[3].e.e.name="alias";assert.notEqual(run("--produce-stateful-source",a,claims).status,0);});
  test("consumer rejects a transfer outside any loop",()=>{const a=structuredClone(ast);sf(a,"stopAfterWrite").body[0]={k:"break",pos:sf(a,"stopAfterWrite").body[0].pos};assert.notEqual(run("--produce-stateful-source",a,claims).status,0);});
  test("sidecars preserve transfer environments and checks",()=>{
    const out=path.join(tmp,"sidecar.json"),r=exec(process.execPath,[path.resolve(__dirname,"../tools/export-source-claims.mts"),file,"--claims",claimsPath,"--out",out,"--verifier",verifier]);assert.equal(r.status,0,r.stderr);
    fs.writeFileSync(ap,JSON.stringify(ast));fs.writeFileSync(ep,JSON.stringify(evidence));const c=exec(verifier,["--check-source-claims",ap,out,file,ep]);assert.equal(c.status,0,c.stderr);
  });
  for(const [name,body] of [
    ["labeled break","while (true) { break outer; } return null;"],
    ["labeled continue","while (true) { continue outer; } return null;"],
    ["closure cannot break its caller's loop","while (true) { const f = (x: null): null => { break; return null; }; } return null;"]
  ])test(`${name} gated`,()=>{const p=path.join(tmp,"gated.ts");fs.writeFileSync(p,`function gated(): null { ${body} }`);assert.notEqual(exec(process.execPath,[path.resolve(__dirname,"../tools/parse-source.mts"),p]).status,0);});
  test("source runtime distinguishes nearest-loop exits and branch transfers",()=>{
    const js=stripTypes(fs.readFileSync(file,"utf8"));
    const values=vm.runInNewContext(js+"; JSON.stringify([stopAfterWrite(),continueAfterWrite(),nestedBreak(true),nestedBreak(false),branchContinue(true),branchContinue(false)])",{},{timeout:2000});
    assert.equal(values,JSON.stringify([false,false,true,false,false,true]));
  });
  console.log(`Loop transfers: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
