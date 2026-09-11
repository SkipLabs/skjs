#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
const [astPath,claimsPath,fileKey,verifier]=process.argv.slice(2);
const ast=JSON.parse(fs.readFileSync(astPath,"utf8")), claims=JSON.parse(fs.readFileSync(claimsPath,"utf8"));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"stateful-closures-"));
const clone=(x: any) =>JSON.parse(JSON.stringify(x));
const sf=(a: any) =>a.functions.find((f: any) =>f.name==="capturedRead");
const cf=(c: any) =>c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="capturedRead");
const at=(c: any,e: any)=>cf(c).exprs.find((x: any) =>x.pos[0]===e.pos[0] && x.pos[1]===e.pos[1]);
const lit=(v: any) =>({top:false,atoms:[{a:"booleanlit",v}]});
let passed=0;
function run(mode: string,a: any,c: any,e?: any) {
  fs.writeFileSync(path.join(tmp,"ast"),JSON.stringify(a));fs.writeFileSync(path.join(tmp,"claims"),JSON.stringify(c));
  if(e) fs.writeFileSync(path.join(tmp,"evidence"),JSON.stringify(e));
  const args=[mode,path.join(tmp,"ast"),path.join(tmp,"claims"),fileKey,path.join(tmp,"evidence")];
  if(mode==="--produce-stateful-source")args.push("10");
  const r=spawnSync(verifier,args,{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;
}
function expect(name: string,r: any,accept: any){if((r.status===0)!==accept)throw Error(`${name}: ${r.status}: ${r.stdout}${r.stderr}`);passed++;console.log(`  ${name}: OK`);}
try {
  expect("produce captured closure certificates",run("--produce-stateful-source",ast,claims),true);
  const evidence=JSON.parse(fs.readFileSync(path.join(tmp,"evidence"),"utf8"));
  expect("independent closure consumer",run("--check-stateful-source",ast,claims,evidence),true);
  for(const [name,edit] of [
    ["missing closure body claim",(a,c)=>{const e=sf(a).body[1].init.body;cf(c).exprs=cf(c).exprs.filter((x: any) =>x.pos[1]!==e.pos[1]||x.pos[0]!==e.pos[0]);}],
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
  ] as [string, (...xs: any[]) => any][]){
    const a=clone(ast),c=clone(claims);edit(a,c);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Each source function has an ordered list of exact supplemental sequents.
  if(evidence.version!==3 || evidence.obligations.length!==ast.functions.length ||
     evidence.obligations.some((es: any) =>es.length===0)) throw Error("missing expression obligations");
  for(const [name,edit] of [
    ["old source bundle rejected", e=>{e.version=2;}],
    ["missing obligation lists", e=>{delete e.obligations;}],
    ["missing function obligations", e=>{e.obligations.pop();}],
    ["missing expression proof", e=>{e.obligations[0].pop();}],
    ["extra expression proof", e=>{e.obligations[0].push(e.obligations[0][0]);}],
    ["valid proof for wrong sequent", e=>{e.obligations[0][1]=clone(e.obligations[0][0]);}],
    ["changed expression context", e=>{e.obligations[0][0].node.claim.context=[];}],
    ["changed expression result", e=>{e.obligations[0][0].node.claim.type=[1];}],
  ] as [string, (...xs: any[]) => any][]) {
    const e=clone(evidence);edit(e);
    expect(name,run("--check-stateful-source",ast,claims,e),false);
  }
  for(const [name,select] of [
    ["writingBody", e=>e.body.rhs],
    ["allocatingBody", e=>e.body.e.e],
    ["callingBody", e=>e.body.arg],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find((f: any) =>f.name===name);
    const closure=f.body.filter((s: any) =>s.init && s.init.k==="lambda").at(-1).init;
    const e=select(closure),fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name===name);
    const claim=fc.exprs.find((q: any) =>q.pos[0]===e.pos[0] && q.pos[1]===e.pos[1]);
    claim.type=lit(name==="allocatingBody" ? "false" : "true");
    expect(`${name} internal claim`,run("--produce-stateful-source",a,c),false);
    expect(`${name} internal claim (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Direct construction must reject the false composite claim without speculative search.
  {
    const c=clone(claims),f=ast.functions.find((f: any) =>f.name==="writingBody");
    const e=f.body[1].init.body,fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="writingBody");
    fc.exprs.find((q: any) =>q.pos[0]===e.pos[0] && q.pos[1]===e.pos[1]).type=lit("true");
    expect("composite write result claim",run("--produce-stateful-source",ast,c),false);
    expect("composite write result claim (consumer)",run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing block entry claim", (fc,pos)=>{fc.envs=fc.envs.filter((q: any) =>q.pos[0]!==pos[0]);}],
    ["missing block parameter", (fc,pos)=>{fc.envs.find((q: any) =>q.pos[0]===pos[0]).vars=fc.envs.find((q: any) =>q.pos[0]===pos[0]).vars.filter((v: any) =>v.name!=="unit");}],
    ["unjustified block entry", (fc,pos)=>{fc.envs.find((q: any) =>q.pos[0]===pos[0]).vars.find((v: any) =>v.name==="unit").type=lit("true");}],
  ] as [string, (...xs: any[]) => any][]) {
    const c=clone(claims),f=ast.functions.find((f: any) =>f.name==="blockReader");
    const fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="blockReader");
    edit(fc,f.body[1].init.body.pos);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing local statement claim", (a,fc)=>{const p=a.body[0].init.body.body.pos;fc.envs=fc.envs.filter((q: any) =>q.pos[0]!==p[0]);}],
    ["wrong local annotation", a=>{a.body[0].init.body.body.annot=lit("true");}],
    ["shadowing local gated", a=>{a.body[0].init.body.body.name="cell";}],
    ["unjustified local entry", (a,fc)=>{const p=a.body[0].init.body.body.body.pos;fc.envs.find((q: any) =>q.pos[0]===p[0]).vars.find((v: any) =>v.name==="saved").type=lit("true");}],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find((f: any) =>f.name==="localBlock");
    const fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="localBlock");
    edit(f,fc);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing branch entry", (b,fc)=>{fc.envs=fc.envs.filter((q: any) =>q.pos[0]!==b.then.pos[0]);}],
    ["wrong false-arm refinement", (b,fc)=>{fc.envs.find((q: any) =>q.pos[0]===b.else_.pos[0]).vars.find((v: any) =>v.name==="flag").type=lit("true");}],
    ["branch cannot narrow parameter", (b,fc)=>{fc.envs.find((q: any) =>q.pos[0]===b.then.pos[0]).vars.find((v: any) =>v.name==="unit").type=lit("true");}],
    ["branch result annotation checked", b=>{b.result=lit("false");}],
    ["non-Boolean closure condition", b=>{b.cond={k:"lit",pos:b.cond.pos,lit:{a:"null"}};}],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find((f: any) =>f.name==="branchingClosure");
    const fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="branchingClosure");
    edit(f.body[0].init.body,fc);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing shared continuation entry", (b,fc)=>{fc.envs=fc.envs.filter((q: any) =>q.pos[0]!==b.body.pos[0]);}],
    ["branch refinement cannot escape join", (b,fc)=>{fc.envs.find((q: any) =>q.pos[0]===b.body.pos[0]).vars.find((v: any) =>v.name==="flag").type=lit("true");}],
    ["branch local cannot escape closure join", b=>{b.body.e={k:"id",pos:b.body.e.pos,name:"saved"};}],
    ["branch local initializer checked", (b,fc)=>{const pos=b.init.then.init.pos;fc.exprs.find((q: any) =>q.pos[0]===pos[0]&&q.pos[1]===pos[1]).type=lit("false");}],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find((f: any) =>f.name==="joinedClosure");
    const fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="joinedClosure");
    edit(f.body[0].init.body.body,fc);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of [
    ["missing early-return continuation entry", (b,fc)=>{fc.envs=fc.envs.filter((q: any) =>q.pos[0]!==b.else_.pos[0]);}],
    ["wrong surviving-arm refinement", (b,fc)=>{fc.envs.find((q: any) =>q.pos[0]===b.else_.pos[0]).vars.find((v: any) =>v.name==="flag").type=lit("true");}],
    ["early return expression claim checked", (b,fc)=>{const pos=b.then.e.pos;fc.exprs.find((q: any) =>q.pos[0]===pos[0]&&q.pos[1]===pos[1]).type=lit("false");}],
  ] as [string, (...xs: any[]) => any][]) {
    const a=clone(ast),c=clone(claims),f=a.functions.find((f: any) =>f.name==="earlyReturn");
    const fc=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="earlyReturn");
    edit(f.body[0].init.body,fc);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  {
    const b=ast.functions.find((f: any) =>f.name==="earlyReturn").body[0].init.body;
    if(b.k!=="ifBody" || b.then.k!=="returnBody" || b.else_.k!=="returnBody" ||
       b.then.pos[0]===b.else_.pos[0]) throw Error("early return must select two distinct returns");
    passed++;console.log("  early return keeps continuation in surviving arm: OK");
    const c=ast.functions.find((f: any) =>f.name==="earlyReturnElse").body[0].init.body.body;
    if(c.k!=="ifBody" || c.else_.k!=="returnBody" || c.then.k!=="seqBody" ||
       c.then.init.k!=="letBody" || c.then.body.k!=="letBody" ||
       c.then.init.name!=="saved" || c.then.body.name!=="saved")
      throw Error("falling arm and continuation need separate local scopes");
    passed++;console.log("  falling arm local scope ends before continuation: OK");
  }
  const parser=path.resolve(__dirname,"../tools/parse-source.mts");
  for(const [name,closure] of [
    ["partially returning nested arm gated","(u: null): boolean => { if (true) { if (true) { return true; } } return false; }"],
    ["missing closure else gated","(u: null): boolean => { if (true) { return true; } }"],
    ["async closure gated","async (u: null): Promise<boolean> => true"],
    ["optional closure parameter gated","(u?: null): boolean => true"],
    ["generic closure gated","<T>(u: T): T => u"],
  ]){
    const file=path.join(tmp,"gate.ts");fs.writeFileSync(file,`function gated(): null { const f = ${closure}; return null; }`);
    const r=spawnSync(process.execPath,[parser,file],{encoding:"utf8"});
    if(r.error||r.signal||r.status!==1||!r.stderr.includes("gate:"))throw Error(`${name}: ${r.stderr}`);
    passed++;console.log(`  ${name}: OK`);
  }
  console.log(`Stateful closures: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
