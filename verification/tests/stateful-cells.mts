#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
// Real cell source claims: production, independent consumption, and corruption.


import type { Ast } from "../tools/fragment.mts";
import type { ClaimType, RecordAtom } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import type { SpawnSyncReturns } from "node:child_process";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { allocField, at as nth, atom, claimAt, claimType, expr, fn, must, rows, stmt } from "./edits.mts";

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "stateful-cells-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const fun = (c: SkjsClaims,n: string) => functionOf(c,fileKey,n);
const source = (a: Ast,n: string) => fn(a,n);
/** The claim stated for one expression of a named function, and the type it
 * states: an alteration replaces the one or changes the other. */
const claim = (c: SkjsClaims,n: string,e: {pos: Span}) => claimAt(fun(c,n),e.pos);
const at = (c: SkjsClaims,n: string,e: {pos: Span}) => claimType(claim(c,n,e));
const bool: ClaimType = {top:false,atoms:[{a:"boolean"}]};
const lit =(v: string): ClaimType => ({top:false,atoms:[{a:"booleanlit",v}]});
/** The cell this fixture allocates, and the statements around it. */
const allocation = (a: Ast,n: string) => stmt(nth(source(a,n).body,0),"const");
let passed = 0;
function run(mode: string,a: Ast,c: SkjsClaims,evidence?: unknown) {
  fs.writeFileSync(path.join(tmp,"ast"),JSON.stringify(a));
  fs.writeFileSync(path.join(tmp,"claims"),JSON.stringify(c));
  if(evidence) fs.writeFileSync(path.join(tmp,"evidence"),JSON.stringify(evidence));
  const r=spawnSync(verifier,[mode,path.join(tmp,"ast"),path.join(tmp,"claims"),fileKey,path.join(tmp,"evidence"),...(mode === "--produce-stateful-source" ? ["10"] : [])],{encoding:"utf8"});
  if(r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
}
function expect(name: string,r: SpawnSyncReturns<string>,accept: boolean) {
  if((r.status===0)!==accept) throw Error(`${name}: ${r.status}: ${r.stdout}${r.stderr}`);
  console.log(`  ${name}: OK`); passed++;
}
try {
  expect("produce cell source certificates",run("--produce-stateful-source",ast,claims),true);
  const evidence=JSON.parse(fs.readFileSync(path.join(tmp,"evidence"),"utf8"));
  expect("independent cell consumer",run("--check-stateful-source",ast,claims,evidence),true);
  // The exporter retains every alternative; only an existing invariant arm
  // may absorb another arm with stronger read/write requirements.
  for (const reverse of [false,true]) {
    const c=clone(claims),e=allocation(ast,"aliasWrite").init;
    const t=at(c,"aliasWrite",e),narrow=clone(atom(t.atoms[0],"record"));
    narrow.fields[0].read=lit("true");
    t.atoms=reverse?[narrow,...t.atoms]:[...t.atoms,narrow];
    expect(`redundant read/write union, reverse=${reverse}`,run("--produce-stateful-source",ast,c),true);
    expect(`same checked certificate after exact absorption, reverse=${reverse}`,run("--check-stateful-source",ast,c,evidence),true);
  }
  for (const [name,edit] of rows<[string, (a: RecordAtom) => void]>([
    ["read variance cannot be reversed",a=>{a.fields[0].read={top:false,atoms:[{a:"boolean"},{a:"null"}]};}],
    ["write variance cannot be reversed",a=>{a.fields[0].write=lit("true");}],
    ["unsupported primitive arm cannot be erased",a=>{a.fields[0].read={top:false,atoms:[{a:"string"}]};}],
    ["optional field cannot be erased",a=>{a.fields[0].optional=true;}],
    ["real index cannot be erased",a=>{a.indexes.string="present";}],
    ["callable requirement cannot be erased",a=>{a.call="present";}],
  ])) {
    const c=clone(claims),t=at(c,"aliasWrite",allocation(ast,"aliasWrite").init);
    const arm=clone(atom(t.atoms[0],"record"));edit(arm);t.atoms.push(arm);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  /** The cell's declared contract, which the source states on the binding. */
  const declared = (a: Ast,n: string) =>
    atom(must(allocation(a,n).annot,"a cell annotation").atoms[0],"record");
  const written = (a: Ast,n: string,i: number) =>
    expr(stmt(nth(source(a,n).body,i),"effect").e,"write");
  const cases: [string, (a: Ast, c: SkjsClaims) => void][] = [
    ["cell parameter boundary",(a,c)=>{const t=must(allocation(a,"aliasWrite").annot,"a cell annotation");source(a,"aliasWrite").params[0].type=clone(t);fun(c,"aliasWrite").params[0].type=clone(t);}],
    ["initializer subexpression claim",(a,c)=>{claim(c,"aliasWrite",allocField(allocation(a,"aliasWrite").init)).type=lit("true");}],
    ["missing allocation subexpression",(a,c)=>{const e=allocField(allocation(a,"aliasWrite").init); fun(c,"aliasWrite").exprs=fun(c,"aliasWrite").exprs.filter((x) =>x.pos[0]!==e.pos[0]);}],
    ["allocation invariant cannot narrow",(a,c)=>{const t=atom(at(c,"aliasWrite",allocation(a,"aliasWrite").init).atoms[0],"record").fields[0];t.read=lit("true");t.write=lit("true");}],
    ["receiver must be a reference",(a,c)=>{claim(c,"aliasWrite",written(a,"aliasWrite",2).receiver).type=bool;}],
    ["write respects invariant",(a,c)=>{const e=expr(written(a,"aliasWrite",2).rhs,"lit");e.lit={a:"null"};claim(c,"aliasWrite",e).type={top:false,atoms:[{a:"null"}]};}],
    ["assignment result is checked",(a,c)=>{claim(c,"assignmentResult",stmt(nth(source(a,"assignmentResult").body,1),"return").e).type=lit("true");}],
    ["post-write read cannot invent refinement",(a,c)=>{claim(c,"aliasWrite",stmt(nth(source(a,"aliasWrite").body,3),"return").e).type=lit("true");}],
    ["setter cannot be forgotten",(a,c)=>{atom(at(c,"aliasWrite",allocation(a,"aliasWrite").init).atoms[0],"record").fields[0].write={top:false,atoms:[]};}],
    ["source cell annotation is enforced",a=>{declared(a,"aliasWrite").fields[0].read=lit("true");declared(a,"aliasWrite").fields[0].write=lit("true");}],
    ["nested assignment claim is checked",(a,c)=>{claim(c,"nestedWrite",written(a,"nestedWrite",1).rhs).type=lit("true");}],
  ];
  for(const [name,edit] of cases) {
    const a=clone(ast),c=clone(claims);edit(a,c);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  const parser=path.resolve(__dirname,"../tools/fragment-parse.mts");
  for (const [name,body] of [
    ["accessor allocation gate","const c = { get value(): boolean { return true; } }; return c.value;"],
    ["spread allocation gate","const c = { value: true }; const d = { ...c }; return d.value;"],
    ["prototype allocation gate","const c = { __proto__: true, value: false }; return c.__proto__;"],
    ["computed property gate","const c = { ['value']: true }; return c.value;"],
    ["optional access gate","const c = { value: true }; return c?.value;"],
  ]) {
    const file=path.join(tmp,"gate.ts");fs.writeFileSync(file,`function gated(): boolean { ${body} }`);
    const r=spawnSync(process.execPath,[parser,file],{encoding:"utf8"});
    if(r.error || r.signal || r.status !== 1 || !r.stderr.includes("gate:")) throw Error(`${name}: ${r.stderr}`);
    passed++;console.log(`  ${name}: OK`);
  }
  console.log(`Stateful cells: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
