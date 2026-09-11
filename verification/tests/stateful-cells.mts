#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
// Real cell source claims: production, independent consumption, and corruption.


const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "stateful-cells-"));
const clone = x => JSON.parse(JSON.stringify(x));
const fun = (c,n) => c.find(f=>f.file===fileKey).functions.find(f=>f.name===n);
const source = (a,n) => a.functions.find(f=>f.name===n);
const at = (c,n,e) => fun(c,n).exprs.find(x=>x.pos[0]===e.pos[0] && x.pos[1]===e.pos[1]);
const bool = {top:false,atoms:[{a:"boolean"}]};
const lit = v => ({top:false,atoms:[{a:"booleanlit",v}]});
let passed = 0;
function run(mode,a,c,evidence?) {
  fs.writeFileSync(path.join(tmp,"ast"),JSON.stringify(a));
  fs.writeFileSync(path.join(tmp,"claims"),JSON.stringify(c));
  if(evidence) fs.writeFileSync(path.join(tmp,"evidence"),JSON.stringify(evidence));
  const r=spawnSync(verifier,[mode,path.join(tmp,"ast"),path.join(tmp,"claims"),fileKey,path.join(tmp,"evidence"),...(mode === "--produce-stateful-source" ? ["10"] : [])],{encoding:"utf8"});
  if(r.error || r.signal) throw r.error || Error(r.signal);
  return r;
}
function expect(name,r,accept) {
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
    const c=clone(claims),e=source(ast,"aliasWrite").body[0].init;
    const t=at(c,"aliasWrite",e).type,narrow=clone(t.atoms[0]);
    narrow.fields[0].read=lit("true");
    t.atoms=reverse?[narrow,...t.atoms]:[...t.atoms,narrow];
    expect(`redundant read/write union, reverse=${reverse}`,run("--produce-stateful-source",ast,c),true);
    expect(`same checked certificate after exact absorption, reverse=${reverse}`,run("--check-stateful-source",ast,c,evidence),true);
  }
  for (const [name,edit] of [
    ["read variance cannot be reversed",a=>{a.fields[0].read={top:false,atoms:[{a:"boolean"},{a:"null"}]};}],
    ["write variance cannot be reversed",a=>{a.fields[0].write=lit("true");}],
    ["unsupported primitive arm cannot be erased",a=>{a.fields[0].read={top:false,atoms:[{a:"string"}]};}],
    ["optional field cannot be erased",a=>{a.fields[0].optional=true;}],
    ["real index cannot be erased",a=>{a.indexes.string="present";}],
    ["callable requirement cannot be erased",a=>{a.call="present";}],
  ] as [string, (...xs: any[]) => any][]) {
    const c=clone(claims),t=at(c,"aliasWrite",source(ast,"aliasWrite").body[0].init).type;
    const arm=clone(t.atoms[0]);edit(arm);t.atoms.push(arm);
    expect(name,run("--produce-stateful-source",ast,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",ast,c,evidence),false);
  }
  const cases: [string, (a: any, c?: any) => void][] = [
    ["cell parameter boundary",(a,c)=>{const t=source(a,"aliasWrite").body[0].annot;source(a,"aliasWrite").params[0].type=clone(t);fun(c,"aliasWrite").params[0].type=clone(t);}],
    ["initializer subexpression claim",(a,c)=>{at(c,"aliasWrite",source(a,"aliasWrite").body[0].init.e).type=lit("true");}],
    ["missing allocation subexpression",(a,c)=>{const e=source(a,"aliasWrite").body[0].init.e; fun(c,"aliasWrite").exprs=fun(c,"aliasWrite").exprs.filter(x=>x.pos[0]!==e.pos[0]);}],
    ["allocation invariant cannot narrow",(a,c)=>{const t=at(c,"aliasWrite",source(a,"aliasWrite").body[0].init).type.atoms[0].fields[0];t.read=lit("true");t.write=lit("true");}],
    ["receiver must be a reference",(a,c)=>{at(c,"aliasWrite",source(a,"aliasWrite").body[2].e.receiver).type=bool;}],
    ["write respects invariant",(a,c)=>{const e=source(a,"aliasWrite").body[2].e.rhs;e.lit={a:"null"};at(c,"aliasWrite",e).type={top:false,atoms:[{a:"null"}]};}],
    ["assignment result is checked",(a,c)=>{at(c,"assignmentResult",source(a,"assignmentResult").body[1].e).type=lit("true");}],
    ["post-write read cannot invent refinement",(a,c)=>{at(c,"aliasWrite",source(a,"aliasWrite").body[3].e).type=lit("true");}],
    ["setter cannot be forgotten",(a,c)=>{at(c,"aliasWrite",source(a,"aliasWrite").body[0].init).type.atoms[0].fields[0].write={top:false,atoms:[]};}],
    ["source cell annotation is enforced",a=>{source(a,"aliasWrite").body[0].annot.atoms[0].fields[0].read=lit("true");source(a,"aliasWrite").body[0].annot.atoms[0].fields[0].write=lit("true");}],
    ["nested assignment claim is checked",(a,c)=>{at(c,"nestedWrite",source(a,"nestedWrite").body[1].e.rhs).type=lit("true");}],
  ];
  for(const [name,edit] of cases) {
    const a=clone(ast),c=clone(claims);edit(a,c);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }
  const parser=path.resolve(__dirname,"../tools/parse-source.mts");
  for (const [name,body] of [
    ["accessor allocation gate","const c = { get value(): boolean { return true; } }; return c.value;"],
    ["spread allocation gate","const c = { value: true }; const d = { ...c }; return d.value;"],
    ["extra-field allocation gate","const c = { value: true, other: false }; return c.value;"],
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
