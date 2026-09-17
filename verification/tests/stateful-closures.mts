#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast, Expr, FunctionAst } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import {
  functionOf,
  type SkjsClaims,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import { allocField, atom, binding, claimAt, claimType, entryAt, expr, field, fn, list, must, at as nth, record, rows, sole, stmt, written } from "./edits.mts";
const __dirname = path.dirname(import.meta.filename);
const [astPath,claimsPath,fileKey,verifier]=process.argv.slice(2);
const ast: Ast=JSON.parse(fs.readFileSync(astPath,"utf8"));
const claims: SkjsClaims=JSON.parse(fs.readFileSync(claimsPath,"utf8"));
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"stateful-closures-"));
const clone=<T,>(x: T): T =>JSON.parse(JSON.stringify(x));
const sf=(a: Ast) =>fn(a,"capturedRead");
const cf=(c: SkjsClaims) =>functionOf(c,fileKey,"capturedRead");
const at=(c: SkjsClaims,e: {pos: Span})=>claimAt(cf(c),e.pos);
const lit=(v: string): ClaimType =>({top:false,atoms:[{a:"booleanlit",v}]});
/** The closure a fixture binds at the i-th statement. */
const lambda=(f: FunctionAst,i: number)=>expr(sole(stmt(nth(f.body,i),"const")).init,"lambda");
type IfBody = Extract<Expr, { k: "ifBody" }>;
type SeqBody = Extract<Expr, { k: "seqBody" }>;
/** The lowered `let` inside the closure `localBlock` binds. */
const local=(f: FunctionAst)=>expr(expr(lambda(f,0).body,"letBody").body,"letBody");
/** The obligations of an evidence bundle, and the first function's own. */
const each=(e: unknown)=>list(field(e,"obligations"),"the obligations");
const first=(e: unknown)=>list(field(e,"obligations",0),"the first obligations");
/** The call `capturedRead` ends with. */
const call=(f: FunctionAst)=>expr(stmt(nth(f.body,4),"return").e,"apply");
/** The last closure a fixture binds, whichever statement binds it. */
const lastLambda=(f: FunctionAst)=>{
  const bound=f.body.filter((s)=>s.k==="const"&&s.bindings.length===1&&s.bindings[0].init.k==="lambda");
  return expr(sole(stmt(must(bound[bound.length-1],"a bound closure"),"const")).init,"lambda");
};
let passed=0;
function run(mode: string,a: Ast,c: SkjsClaims,e?: unknown) {
  fs.writeFileSync(path.join(tmp,"ast"),JSON.stringify(a));fs.writeFileSync(path.join(tmp,"claims"),JSON.stringify(c));
  if(e) fs.writeFileSync(path.join(tmp,"evidence"),JSON.stringify(e));
  const args=[mode,path.join(tmp,"ast"),path.join(tmp,"claims"),fileKey,path.join(tmp,"evidence")];
  if(mode==="--produce-stateful-source")args.push("10");
  const r=spawnSync(verifier,args,{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;
}
function expect(name: string,r: {status: number|null; stdout: string; stderr: string},accept: boolean){if((r.status===0)!==accept)throw Error(`${name}: ${r.status}: ${r.stdout}${r.stderr}`);passed++;console.log(`  ${name}: OK`);}
try {
  expect("produce captured closure certificates",run("--produce-stateful-source",ast,claims),true);
  const evidence=JSON.parse(fs.readFileSync(path.join(tmp,"evidence"),"utf8"));
  expect("independent closure consumer",run("--check-stateful-source",ast,claims,evidence),true);
  for(const [name,edit] of rows<[string, (a: Ast, c: SkjsClaims) => void]>([
    ["missing closure body claim",(a,c)=>{const e=lambda(sf(a),1).body;cf(c).exprs=cf(c).exprs.filter((x) =>x.pos[1]!==e.pos[1]||x.pos[0]!==e.pos[0]);}],
    ["body claim cannot narrow",(a,c)=>{at(c,lambda(sf(a),1).body).type=lit("true");}],
    ["capture claim must match binding",(a,c)=>{at(c,expr(lambda(sf(a),1).body,"read").e).type=lit("true");}],
    ["unbound capture rejected",a=>{expr(expr(lambda(sf(a),1).body,"read").e,"id").name="missing";}],
    ["closure signature cannot narrow",(a,c)=>{atom(claimType(at(c,lambda(sf(a),1))).atoms[0],"function").result=lit("true");}],
    ["closure annotation checked",a=>{lambda(sf(a),1).result=lit("true");}],
    ["consistent false closure claim",(a,c)=>{const e=lambda(sf(a),1);e.result=lit("true");atom(claimType(at(c,e)).atoms[0],"function").result=lit("true");at(c,e.body).type=lit("true");}],
    ["wrong call result",(a,c)=>{at(c,stmt(nth(sf(a).body,4),"return").e).type=lit("true");}],
    ["wrong call argument",(a,c)=>{const e=expr(must(call(sf(a)).args[0],"an argument"),"lit");e.lit={a:"booleanlit",v:"true"};at(c,e).type=lit("true");}],
    ["callee claim is checked",(a,c)=>{at(c,call(sf(a)).callee).type=lit("true");}],
    ["shadowing closure parameter gated",a=>{must(lambda(sf(a),1).params[0],"a parameter").name="cell";}],
    ["obsolete lambda field rejected",a=>{written(lambda(sf(a),1)).name="ignored";}],
    ["function requirements cannot disappear",(a,c)=>{atom(claimType(at(c,lambda(sf(a),1))).atoms[0],"function").construct="present";}],
    ["extra signature fields rejected",(a,c)=>{written(atom(claimType(at(c,lambda(sf(a),1))).atoms[0],"function")).optional=true;}],
  ])){
    const a=clone(ast),c=clone(claims);edit(a,c);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Each source function has an ordered list of exact supplemental sequents.
  const obligations=list(field(evidence,"obligations"),"the obligations");
  if(obligations.length!==ast.functions.length ||
     obligations.some((es) =>list(es,"one function's obligations").length===0))
    throw Error("missing expression obligations");
  for(const [name,edit] of rows<[string, (e: unknown) => void]>([
    ["unknown bundle fields", e=>{record(e,"the evidence").status="verified";}],
    ["missing obligation lists", e=>{delete record(e,"the evidence").obligations;}],
    ["missing function obligations", e=>{each(e).pop();}],
    ["missing expression proof", e=>{first(e).pop();}],
    ["extra expression proof", e=>{first(e).push(first(e)[0]);}],
    ["valid proof for wrong sequent", e=>{first(e)[1]=clone(first(e)[0]);}],
    ["changed expression context", e=>{record(field(first(e)[0],"node","claim"),"a claim").context=[];}],
    ["changed expression result", e=>{record(field(first(e)[0],"node","claim"),"a claim").type=[1];}],
  ])) {
    const e=clone(evidence);edit(e);
    expect(name,run("--check-stateful-source",ast,claims,e),false);
  }
  for(const [name,select] of rows<[string, (body: Expr) => Expr]>([
    ["writingBody", body=>expr(body,"write").rhs],
    ["allocatingBody", body=>allocField(expr(body,"read").e)],
    ["callingBody", body=>must(expr(body,"apply").args[0],"an argument")],
  ])) {
    const a=clone(ast),c=clone(claims);
    const e=select(lastLambda(fn(a,name)).body);
    const claim=claimAt(functionOf(c,fileKey,name),e.pos);
    claim.type=lit(name==="allocatingBody" ? "false" : "true");
    expect(`${name} internal claim`,run("--produce-stateful-source",a,c),false);
    expect(`${name} internal claim (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  // Direct construction must reject the false composite claim without speculative search.
  {
    const c=clone(claims);
    const e=lambda(fn(ast,"writingBody"),1).body;
    claimAt(functionOf(c,fileKey,"writingBody"),e.pos).type=lit("true");
    expect("composite write result claim",run("--produce-stateful-source",ast,c),false);
    expect("composite write result claim (consumer)",run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (fc: SkjsFunction, pos: Span) => void]>([
    ["missing block entry claim", (fc,pos)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==pos[0]);}],
    ["missing block parameter", (fc,pos)=>{const e=entryAt(fc,pos[0]);e.vars=e.vars.filter((v) =>v.name!=="unit");}],
    ["unjustified block entry", (fc,pos)=>{binding(fc,pos[0],"unit").type=lit("true");}],
  ])) {
    const c=clone(claims);
    edit(functionOf(c,fileKey,"blockReader"),lambda(fn(ast,"blockReader"),1).body.pos);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (a: FunctionAst, fc: SkjsFunction) => void]>([
    ["missing local statement claim", (a,fc)=>{const p=local(a).pos;fc.envs=fc.envs.filter((q) =>q.pos[0]!==p[0]);}],
    ["wrong local annotation", a=>{local(a).annot=lit("true");}],
    ["shadowing local gated", a=>{local(a).name="cell";}],
    ["unjustified local entry", (a,fc)=>{binding(fc,expr(local(a).body,"letBody").pos[0],"saved").type=lit("true");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(fn(a,"localBlock"),functionOf(c,fileKey,"localBlock"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (b: IfBody, fc: SkjsFunction) => void]>([
    ["missing branch entry", (b,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==b.then.pos[0]);}],
    ["wrong false-arm refinement", (b,fc)=>{binding(fc,b.else_.pos[0],"flag").type=lit("true");}],
    ["branch cannot narrow parameter", (b,fc)=>{binding(fc,b.then.pos[0],"unit").type=lit("true");}],
    ["branch result annotation checked", b=>{b.result=lit("false");}],
    ["non-Boolean closure condition", b=>{b.cond={k:"lit",pos:b.cond.pos,lit:{a:"null"}};}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(expr(lambda(fn(a,"branchingClosure"),0).body,"ifBody"),functionOf(c,fileKey,"branchingClosure"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (b: SeqBody, fc: SkjsFunction) => void]>([
    ["missing shared continuation entry", (b,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==b.body.pos[0]);}],
    ["branch refinement cannot escape join", (b,fc)=>{binding(fc,b.body.pos[0],"flag").type=lit("true");}],
    ["branch local cannot escape closure join", b=>{const ret=expr(b.body,"returnBody");ret.e={k:"id",pos:ret.e.pos,name:"saved"};}],
    ["branch local initializer checked", (b,fc)=>{const pos=expr(expr(b.init,"ifBody").then,"letBody").init.pos;claimAt(fc,pos).type=lit("false");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(expr(expr(lambda(fn(a,"joinedClosure"),0).body,"letBody").body,"seqBody"),
      functionOf(c,fileKey,"joinedClosure"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (b: IfBody, fc: SkjsFunction) => void]>([
    ["missing early-return continuation entry", (b,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==b.else_.pos[0]);}],
    ["wrong surviving-arm refinement", (b,fc)=>{binding(fc,b.else_.pos[0],"flag").type=lit("true");}],
    ["early return expression claim checked", (b,fc)=>{claimAt(fc,expr(b.then,"returnBody").e.pos).type=lit("false");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(expr(lambda(fn(a,"earlyReturn"),0).body,"ifBody"),functionOf(c,fileKey,"earlyReturn"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  {
    const b=lambda(fn(ast,"earlyReturn"),0).body;
    if(b.k!=="ifBody" || b.then.k!=="returnBody" || b.else_.k!=="returnBody" ||
       b.then.pos[0]===b.else_.pos[0]) throw Error("early return must select two distinct returns");
    passed++;console.log("  early return keeps continuation in surviving arm: OK");
    const c=expr(lambda(fn(ast,"earlyReturnElse"),0).body,"letBody").body;
    if(c.k!=="ifBody" || c.else_.k!=="returnBody" || c.then.k!=="seqBody" ||
       c.then.init.k!=="letBody" || c.then.body.k!=="letBody" ||
       c.then.init.name!=="saved" || c.then.body.name!=="saved")
      throw Error("falling arm and continuation need separate local scopes");
    passed++;console.log("  falling arm local scope ends before continuation: OK");
  }
  const parser=path.resolve(__dirname,"../tools/fragment-parse.mts");
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
