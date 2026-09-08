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
  const parser=path.resolve(__dirname,"../tools/parse-source.js");
  for(const [name,closure] of [
    ["block closure gated","(u: null): boolean => { return true; }"],
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
