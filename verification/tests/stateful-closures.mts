#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast, Expr, FunctionAst, Stmt } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import {
  functionOf,
  type SkjsClaims,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import { allocField, atom, binding, claimAt, claimType, entryAt, expr, field, fn, list, must, at as nth, record, rows, sole, sourceType, stmt, written } from "./edits.mts";
import { claimOfTerm } from "../tools/term-claim.mts";
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
type If = Extract<Stmt, { k: "if" }>;
/** The statements of a closure's block body. */
const block=(e: Expr)=>expr(e,"blockBody").body;
/** The closure `localBlock` binds: its statements. */
const localStmts=(f: FunctionAst)=>block(lambda(f,0).body);
/** The `const saved` declaration inside it. */
const local=(f: FunctionAst)=>sole(stmt(nth(localStmts(f),1),"const"));
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
    ["closure annotation checked",a=>{lambda(sf(a),1).result=sourceType(lit("true"));}],
    ["consistent false closure claim",(a,c)=>{const e=lambda(sf(a),1);e.result=sourceType(lit("true"));atom(claimType(at(c,e)).atoms[0],"function").result=lit("true");at(c,e.body).type=lit("true");}],
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
    edit(functionOf(c,fileKey,"blockReader"),nth(block(lambda(fn(ast,"blockReader"),1).body),0).pos);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (a: FunctionAst, fc: SkjsFunction) => void]>([
    ["missing local statement claim", (a,fc)=>{const p=nth(localStmts(a),1).pos;fc.envs=fc.envs.filter((q) =>q.pos[0]!==p[0]);}],
    ["wrong local annotation", a=>{local(a).annot=sourceType(lit("true"));}],
    ["shadowing local gated", a=>{local(a).name="cell";}],
    ["unjustified local entry", (a,fc)=>{binding(fc,nth(localStmts(a),2).pos[0],"saved").type=lit("true");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(fn(a,"localBlock"),functionOf(c,fileKey,"localBlock"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  const thenAt=(b: If)=>nth(b.then,0).pos, elseAt=(b: If)=>nth(must(b.else_,"an else arm"),0).pos;
  for (const [name,edit] of rows<[string, (b: If, fc: SkjsFunction, a: FunctionAst) => void]>([
    ["missing branch entry", (b,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==thenAt(b)[0]);}],
    ["wrong false-arm refinement", (b,fc)=>{binding(fc,elseAt(b)[0],"flag").type=lit("true");}],
    ["branch cannot narrow parameter", (b,fc)=>{binding(fc,thenAt(b)[0],"unit").type=lit("true");}],
    ["closure result annotation checked", (b,fc,a)=>{lambda(a,0).result=sourceType(lit("false"));}],
    ["non-Boolean closure condition", b=>{b.cond={k:"lit",pos:b.cond.pos,lit:{a:"null"}};}],
  ])) {
    const a=clone(ast),c=clone(claims);
    const f=fn(a,"branchingClosure");
    edit(stmt(nth(block(lambda(f,0).body),0),"if"),functionOf(c,fileKey,"branchingClosure"),f);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (ss: Stmt[], fc: SkjsFunction) => void]>([
    ["missing shared continuation entry", (ss,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==nth(ss,2).pos[0]);}],
    ["branch refinement cannot escape join", (ss,fc)=>{binding(fc,nth(ss,2).pos[0],"flag").type=lit("true");}],
    ["branch local cannot escape closure join", ss=>{const ret=stmt(nth(ss,2),"return");ret.e={k:"id",pos:ret.e.pos,name:"saved"};}],
    ["branch local initializer checked", (ss,fc)=>{const pos=sole(stmt(nth(stmt(nth(ss,1),"if").then,0),"const")).init.pos;claimAt(fc,pos).type=lit("false");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(block(lambda(fn(a,"joinedClosure"),0).body),functionOf(c,fileKey,"joinedClosure"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  for (const [name,edit] of rows<[string, (ss: Stmt[], fc: SkjsFunction) => void]>([
    ["missing early-return continuation entry", (ss,fc)=>{fc.envs=fc.envs.filter((q) =>q.pos[0]!==nth(ss,1).pos[0]);}],
    ["wrong surviving-arm refinement", (ss,fc)=>{binding(fc,nth(ss,1).pos[0],"flag").type=lit("true");}],
    ["early return expression claim checked", (ss,fc)=>{claimAt(fc,stmt(nth(stmt(nth(ss,0),"if").then,0),"return").e.pos).type=lit("false");}],
  ])) {
    const a=clone(ast),c=clone(claims);
    edit(block(lambda(fn(a,"earlyReturn"),0).body),functionOf(c,fileKey,"earlyReturn"));
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  {
    // A closure's body is its statements, as a function's is.
    const b=block(lambda(fn(ast,"earlyReturn"),0).body);
    if(b.length!==2 || nth(b,0).k!=="if" || nth(b,1).k!=="return")
      throw Error("an early return is an `if` and the return after it");
    passed++;console.log("  early return keeps its continuation after the `if`: OK");
    const c=block(lambda(fn(ast,"earlyReturnElse"),0).body);
    if(c.length!==4 || nth(c,1).k!=="if" || nth(c,2).k!=="const")
      throw Error("the falling arm's local and the later one are separate declarations");
    passed++;console.log("  falling arm local scope ends before continuation: OK");
  }
  const parser=path.resolve(__dirname,"../tools/fragment-parse.mts");
  for(const [name,closure] of [
    ["async closure gated","async (u: null): Promise<boolean> => true"],
    ["required parameter after an optional one gated","(u?: null, v: boolean): boolean => true"],
  ]){
    const file=path.join(tmp,"gate.ts");fs.writeFileSync(file,`function gated(): null { const f = ${closure}; return null; }`);
    const r=spawnSync(process.execPath,[parser,file],{encoding:"utf8"});
    if(r.error||r.signal||r.status!==1||!r.stderr.includes("gate:"))throw Error(`${name}: ${r.stderr}`);
    passed++;console.log(`  ${name}: OK`);
  }
  // An optional parameter is not a second arity record: the fragment carries
  // it as the union the body reads, and a call omits that trailing position.
  {
    const file=path.join(tmp,"optional.ts");
    fs.writeFileSync(file,`function opt(): null { const f = (u?: null): boolean => true; return null; }`);
    const r=spawnSync(process.execPath,[parser,file],{encoding:"utf8"});
    if(r.status!==0)throw Error(`optional closure parameter accepted: ${r.stderr}`);
    const ast: Ast = JSON.parse(r.stdout);
    const params=lambda(fn(ast,"opt"),0).params;
    const atoms=claimOfTerm(params[0].type).atoms.map((a:{a:string})=>a.a).sort();
    if(JSON.stringify(atoms)!==JSON.stringify(["null","undefined"]))
      throw Error(`optional closure parameter type: ${JSON.stringify(params[0].type)}`);
    passed++;console.log("  optional closure parameter reads its union: OK");
  }
  console.log(`Stateful closures: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
