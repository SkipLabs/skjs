#!/usr/bin/env node
"use strict";
const fs=require("fs"),os=require("os"),path=require("path");
const {spawnSync}=require("child_process");
const [astPath,claimsPath,fileKey,verifier]=process.argv.slice(2);
const ast=JSON.parse(fs.readFileSync(astPath,"utf8")), claims=JSON.parse(fs.readFileSync(claimsPath,"utf8"));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"stateful-closures-"));
const clone=x=>JSON.parse(JSON.stringify(x));
const sf=a=>a.functions.find(f=>f.name==="capturedRead");
const cf=c=>c.find(f=>f.file===fileKey).functions.find(f=>f.name==="capturedRead");
const at=(c,e)=>cf(c).exprs.find(x=>x.pos[0]===e.pos[0] && x.pos[1]===e.pos[1]);
const lit=v=>({top:false,atoms:[{a:"booleanlit",v}]});
let passed=0;
function run(mode,a,c,e) {
  fs.writeFileSync(path.join(tmp,"ast"),JSON.stringify(a));fs.writeFileSync(path.join(tmp,"claims"),JSON.stringify(c));
  if(e) fs.writeFileSync(path.join(tmp,"evidence"),JSON.stringify(e));
  const args=[mode,path.join(tmp,"ast"),path.join(tmp,"claims"),fileKey,path.join(tmp,"evidence")];
  if(mode==="--produce-stateful-source")args.push("10");
  const r=spawnSync(verifier,args,{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(r.signal);return r;
}
function expect(name,r,accept){if((r.status===0)!==accept)throw Error(`${name}: ${r.status}: ${r.stdout}${r.stderr}`);passed++;console.log(`  ${name}: OK`);}
try {
  expect("produce captured closure certificates",run("--produce-stateful-source",ast,claims),true);
  const evidence=JSON.parse(fs.readFileSync(path.join(tmp,"evidence"),"utf8"));
  expect("independent closure consumer",run("--check-stateful-source",ast,claims,evidence),true);
  for(const [name,edit] of [
    ["missing closure body claim",(a,c)=>{const e=sf(a).body[1].init.body;cf(c).exprs=cf(c).exprs.filter(x=>x.pos[1]!==e.pos[1]||x.pos[0]!==e.pos[0]);}],
    ["body claim cannot narrow",(a,c)=>{at(c,sf(a).body[1].init.body).type=lit("true");}],
    ["capture claim must match binding",(a,c)=>{at(c,sf(a).body[1].init.body.e).type=lit("true");}],
    ["unbound capture rejected",a=>{sf(a).body[1].init.body.e.name="missing";}],
    ["closure signature cannot narrow",(a,c)=>{at(c,sf(a).body[1].init).type.atoms[0].result=lit("true");}],
    ["closure annotation checked",a=>{sf(a).body[1].init.result=lit("true");}],
    ["consistent false closure claim",(a,c)=>{const e=sf(a).body[1].init;e.result=lit("true");at(c,e).type.atoms[0].result=lit("true");at(c,e.body).type=lit("true");}],
    ["wrong call result",(a,c)=>{at(c,sf(a).body[4].e).type=lit("true");}],
    ["wrong call argument",(a,c)=>{const e=sf(a).body[4].e.arg;e.lit={a:"booleanlit",v:"true"};at(c,e).type=lit("true");}],
    ["callee claim is checked",(a,c)=>{at(c,sf(a).body[4].e.callee).type=lit("true");}],
    ["shadowing closure parameter gated",a=>{sf(a).body[1].init.name="cell";}],
    ["function requirements cannot disappear",(a,c)=>{at(c,sf(a).body[1].init).type.atoms[0].construct="present";}],
    ["extra signature fields rejected",(a,c)=>{at(c,sf(a).body[1].init).type.atoms[0].optional=true;}],
  ]){
    const a=clone(ast),c=clone(claims);edit(a,c);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Each source function has an ordered list of exact supplemental sequents.
  if(evidence.version!==3 || evidence.obligations.length!==ast.functions.length ||
     evidence.obligations.some(es=>es.length===0)) throw Error("missing expression obligations");
  for(const [name,edit] of [
    ["old source bundle rejected", e=>{e.version=2;}],
    ["missing obligation lists", e=>{delete e.obligations;}],
    ["missing function obligations", e=>{e.obligations.pop();}],
    ["missing expression proof", e=>{e.obligations[0].pop();}],
    ["extra expression proof", e=>{e.obligations[0].push(e.obligations[0][0]);}],
    ["valid proof for wrong sequent", e=>{e.obligations[0][1]=clone(e.obligations[0][0]);}],
    ["changed expression context", e=>{e.obligations[0][0].node.claim.context=[];}],
    ["changed expression result", e=>{e.obligations[0][0].node.claim.type=[1];}],
  ]) {
    const e=clone(evidence);edit(e);
    expect(name,run("--check-stateful-source",ast,claims,e),false);
  }
  for(const [name,select] of [
    ["writingBody", e=>e.body.rhs],
    ["allocatingBody", e=>e.body.e.e],
    ["callingBody", e=>e.body.arg],
  ]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find(f=>f.name===name);
    const closure=f.body.filter(s=>s.init && s.init.k==="lambda").at(-1).init;
    const e=select(closure),fc=c.find(f=>f.file===fileKey).functions.find(f=>f.name===name);
    const claim=fc.exprs.find(q=>q.pos[0]===e.pos[0] && q.pos[1]===e.pos[1]);
    claim.type=lit(name==="allocatingBody" ? "false" : "true");
    expect(`${name} internal claim`,run("--produce-stateful-source",a,c),false);
    expect(`${name} internal claim (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Direct construction must reject the false composite claim without speculative search.
  {
    const c=clone(claims),f=ast.functions.find(f=>f.name==="writingBody");
    const e=f.body[1].init.body,fc=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="writingBody");
    fc.exprs.find(q=>q.pos[0]===e.pos[0] && q.pos[1]===e.pos[1]).type=lit("true");
    expect("composite write result claim",run("--produce-stateful-source",ast,c),false);
    expect("composite write result claim (consumer)",run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing block entry claim", (fc,pos)=>{fc.envs=fc.envs.filter(q=>q.pos[0]!==pos[0]);}],
    ["missing block parameter", (fc,pos)=>{fc.envs.find(q=>q.pos[0]===pos[0]).vars=fc.envs.find(q=>q.pos[0]===pos[0]).vars.filter(v=>v.name!=="unit");}],
    ["unjustified block entry", (fc,pos)=>{fc.envs.find(q=>q.pos[0]===pos[0]).vars.find(v=>v.name==="unit").type=lit("true");}],
  ]) {
    const c=clone(claims),f=ast.functions.find(f=>f.name==="blockReader");
    const fc=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="blockReader");
    edit(fc,f.body[1].init.body.pos);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing local statement claim", (a,fc)=>{const p=a.body[0].init.body.body.pos;fc.envs=fc.envs.filter(q=>q.pos[0]!==p[0]);}],
    ["wrong local annotation", a=>{a.body[0].init.body.body.annot=lit("true");}],
    ["shadowing local gated", a=>{a.body[0].init.body.body.name="cell";}],
    ["unjustified local entry", (a,fc)=>{const p=a.body[0].init.body.body.body.pos;fc.envs.find(q=>q.pos[0]===p[0]).vars.find(v=>v.name==="saved").type=lit("true");}],
  ]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find(f=>f.name==="localBlock");
    const fc=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="localBlock");
    edit(f,fc);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  const parser=path.resolve(__dirname,"../tools/parse-source.js");
  for(const [name,closure] of [
    ["branching closure gated","(u: null): boolean => { if (true) { return true; } else { return false; } }"],
    ["async closure gated","async (u: null): Promise<boolean> => true"],
    ["optional closure parameter gated","(u?: null): boolean => true"],
    ["generic closure gated","<T>(u: T): T => u"],
  ]){
    const file=path.join(tmp,"gate.ts");fs.writeFileSync(file,`function gated(): null { const f = ${closure}; return null; }`);
    const r=spawnSync(process.execPath,[parser,file,"--stateful"],{encoding:"utf8"});
    if(r.error||r.signal||r.status!==1||!r.stderr.includes("gate:"))throw Error(`${name}: ${r.stderr}`);
    passed++;console.log(`  ${name}: OK`);
  }
  console.log(`Stateful closures: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
