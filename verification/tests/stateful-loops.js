"use strict";
const fs=require("fs"),path=require("path"),os=require("os"),assert=require("assert"),vm=require("vm"),ts=require(require.resolve("typescript",{paths:[path.resolve(__dirname,"../tools")]}));
const {spawnSync}=require("child_process");
const [astPath,claimsPath,file,verifier]=process.argv.slice(2),ast=JSON.parse(fs.readFileSync(astPath)),claims=JSON.parse(fs.readFileSync(claimsPath));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"while-source-"));
const clone=structuredClone, fn=(a,name)=>a.functions.find(f=>f.name===name), cf=(c,name)=>c.find(f=>f.file===file).functions.find(f=>f.name===name);
const ap=path.join(tmp,"ast.json"),cp=path.join(tmp,"claims.json"),ep=path.join(tmp,"evidence.json");
let passed=0;
const test=(name,f)=>{f();passed++;console.log(`  ${name}: OK`);};
const exec=(exe,args)=>{const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000});if(r.error||r.signal)throw r.error||Error(r.signal);return r;};
const run=(mode,a,c,e)=>{fs.writeFileSync(ap,JSON.stringify(a));fs.writeFileSync(cp,JSON.stringify(c));if(e)fs.writeFileSync(ep,JSON.stringify(e));return exec(verifier,[mode,ap,cp,file,ep,...(mode.startsWith("--produce")?["10"]:[])]);};
try {
  test("real SKJS loop claims produce evidence",()=>{const r=run("--produce-stateful-source",ast,claims);assert.equal(r.status,0,r.stderr);});
  const evidence=JSON.parse(fs.readFileSync(ep));
  test("independent loop consumer",()=>assert.equal(run("--check-stateful-source",ast,claims,evidence).status,0));
  for(const [name,edit] of [
    ["missing loop-head invariant",(a,c)=>{const p=fn(a,"oneWrite").body[2].pos[0];cf(c,"oneWrite").envs=cf(c,"oneWrite").envs.filter(e=>e.pos[0]!==p);}],
    ["unjustified loop-head narrowing",(a,c)=>{const p=fn(a,"zeroTrips").body[0].pos[0];cf(c,"zeroTrips").envs.find(e=>e.pos[0]===p).vars.find(v=>v.name==="flag").type={top:false,atoms:[{a:"booleanlit",v:"true"}]};}],
    ["missing repeated condition claim",(a,c)=>{const p=fn(a,"oneWrite").body[2].cond.pos;cf(c,"oneWrite").exprs=cf(c,"oneWrite").exprs.filter(e=>JSON.stringify(e.pos)!==JSON.stringify(p));}],
    ["body local cannot escape the loop",a=>{fn(a,"oneWrite").body[3].e.e.name="alias";}],
    ["nonboolean condition",a=>{const loop=fn(a,"zeroTrips").body[0];loop.cond={k:"lit",pos:loop.cond.pos,lit:{a:"null"}};}],
    ["missing exit return",a=>{fn(a,"zeroTrips").body.pop();}]
  ])test(name,()=>{const a=clone(ast),c=clone(claims);edit(a,c);assert.notEqual(run("--produce-stateful-source",a,c).status,0);assert.notEqual(run("--check-stateful-source",a,c,evidence).status,0);});
  test("back-edge evidence cannot be omitted",()=>{const e=clone(evidence),i=ast.functions.findIndex(f=>f.name==="oneWrite");assert.equal(e.functions[i].certificate[4].expression.node.claim.context.length,5);e.functions[i].certificate[4].edges=[];assert.notEqual(run("--check-stateful-source",ast,claims,e).status,0);});
  test("changed loop body cannot reuse old evidence",()=>{
    const a=clone(ast),c=clone(claims),rhs=fn(a,"oneWrite").body[2].body[1].e.rhs;rhs.lit.v="true";
    cf(c,"oneWrite").exprs.find(e=>JSON.stringify(e.pos)===JSON.stringify(rhs.pos)).type={top:false,atoms:[{a:"booleanlit",v:"true"}]};
    assert.notEqual(run("--check-stateful-source",a,c,evidence).status,0);
    const r=run("--produce-stateful-source",a,c);assert.equal(r.status,0,r.stderr); // A safe infinite loop is permitted.
  });
  test("sidecar conversion preserves cyclic requests",()=>{
    const out=path.join(tmp,"sidecar.json");const r=exec(process.execPath,[path.resolve(__dirname,"../tools/export-source-claims.js"),file,"--claims",claimsPath,"--out",out,"--verifier",verifier]);assert.equal(r.status,0,r.stderr);
    fs.writeFileSync(ap,JSON.stringify(ast));fs.writeFileSync(ep,JSON.stringify(evidence));const checked=exec(verifier,["--check-source-claims",ap,out,file,ep]);assert.equal(checked.status,0,checked.stderr);
  });
  for(const [name,text] of [
    ["break remains gated","while (true) { break; } return null;"],
    ["continue remains gated","while (true) { continue; } return null;"],
    ["nonblock loop body gated","while (false) return null; return null;"],
    ["for remains gated","for (;;) {} return null;"],
    ["closure loop remains gated","const f: (x: null) => null = (x: null): null => { while (false) {} return null; }; return null;"]
  ])test(name,()=>{const file=path.join(tmp,"gated.ts");fs.writeFileSync(file,`function gated(): null { ${text} }`);const r=exec(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),file,"--stateful"]);assert.notEqual(r.status,0);assert(r.stderr.startsWith("gate:"));});
  test("runtime samples agree on zero iterations, one write and nested return",()=>{
    const js=ts.transpileModule(fs.readFileSync(file,"utf8"),{compilerOptions:{target:ts.ScriptTarget.ES2020}}).outputText;
    const actual=vm.runInNewContext(js+"; JSON.stringify([zeroTrips(false),oneWrite(),nested(false),nested(true)])",{},{timeout:2000});
    assert.equal(actual,JSON.stringify([false,false,false,true]));
  });
  console.log(`Stateful loops: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
