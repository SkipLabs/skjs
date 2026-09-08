#!/usr/bin/env node
"use strict";
const fs=require("fs"),path=require("path"),os=require("os"),assert=require("assert");
const {spawnSync}=require("child_process");
const {hash,render,fromSkjs,compareClaims}=require("../tools/annotate-source.js");
const [claimsPath,fileKey,verifier]=process.argv.slice(2);
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"annotated-tests-"));
let passed=0;
const test=(name,f)=>{f();passed++;console.log(`  ${name}: OK`);};
try {
  const source='// Unicode: 😀\nfunction f(x: boolean): boolean { return x; }\n';
  const ns=source.indexOf("f("), es=source.lastIndexOf("x;");
  const report={version:1,source:{file:"test.ts",sha256:hash(source)},producer:"other-analyzer",
    functions:[{name:"f",namePos:[ns,ns+1],entries:[{pos:[source.indexOf("return"),es+2],bindings:[{name:"x",type:"boolean"}]}],
      expressions:[{pos:[es,es+1],type:"boolean"}]}]};
  test("independent producer report and Unicode positions",()=>assert(render(source,report).includes("producer=other-analyzer")));
  test("claims do not imply verification",()=>assert(render(source,report).includes("verification=not-run")));
  test("stale source rejected",()=>assert.throws(()=>render(source+" ",report),/fingerprint/));
  test("duplicate expression attachment rejected",()=>{const r=structuredClone(report);r.functions[0].expressions.push(r.functions[0].expressions[0]);assert.throws(()=>render(source,r),/duplicate/);});
  test("inside-token attachment rejected",()=>{const r=structuredClone(report);r.functions[0].expressions[0].pos=[source.indexOf("return")+1,source.indexOf("return")+3];assert.throws(()=>render(source,r),/attach/);});
  test("comment injection stays inside report",()=>{const r=structuredClone(report);r.functions[0].expressions[0].type='*/ throw "bad"; /*\n';assert(render(source,r).includes('*\\/'));});
  test("return line break remains unchanged",()=>{const s=source.replace("return x","return\nx"),r=structuredClone(report);r.source.sha256=hash(s);r.functions[0].entries=[];r.functions[0].expressions=[];assert(render(s,r).includes("return\nx"));});
  test("stored generic statuses cannot establish verification",()=>{const r=structuredClone(report);r.results=[{status:"verified"}];assert(!render(source,r).includes("verification=verified"));});
  test("comparison ignores stored statuses and provenance changes",()=>{const r=structuredClone(report);r.results=[{status:"verified"}];r.producer="manual";assert.deepEqual(compareClaims(source,report,r).changes,[]);});
  test("comparison reports added removed and changed claims",()=>{
    const r=structuredClone(report);r.functions[0].entries=[];r.functions[0].expressions[0].type="true";
    const changes=compareClaims(source,report,r).changes;
    assert.equal(changes.find(c=>c.kind==="entry").status,"removed");
    assert.equal(changes.find(c=>c.kind==="expression").status,"changed");
    assert.equal(compareClaims(source,r,report).changes.find(c=>c.kind==="entry").status,"added");
    assert(render(source,r,null,{claimChanges:changes}).includes("claim edit: changed expression"));
  });
  test("comparison rejects stale or mismatched baseline",()=>{
    const r=structuredClone(report);r.source.sha256="stale";assert.throws(()=>compareClaims(source,r,report),/fingerprint/);
    r.source.file="other.ts";assert.throws(()=>compareClaims(source,r,report),/identity/);
  });
  test("comparison ignores object property and binding order",()=>{
    const a=structuredClone(report),b=structuredClone(report);
    a.functions[0].entries[0].bindings.push({name:"z",type:"null"});
    b.functions[0].entries[0].bindings=[{type:"null",name:"z"},{type:"boolean",name:"x"}];
    assert.deepEqual(compareClaims(source,a,b).changes,[]);
  });
  const script=path.resolve(__dirname,"../tools/annotate-source.js");
  const generic=path.join(tmp,"generic.ts"), gp=path.join(tmp,"generic.json"), go=path.join(tmp,"generic.annotated.ts");
  fs.writeFileSync(generic,source);fs.writeFileSync(gp,JSON.stringify(report));
  const cli=args=>{const r=spawnSync(process.execPath,[script,...args],{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(r.signal);return r;};
  test("generic claims CLI writes separate source and manifest",()=>{const r=cli([generic,"--claims",gp,"--format","report","--out",go]);assert.equal(r.status,0,r.stderr);assert.equal(fs.readFileSync(generic,"utf8"),source);const m=JSON.parse(fs.readFileSync(go+".json"));assert.equal(m.annotatedSha256,hash(fs.readFileSync(go)));});
  test("existing report is not overwritten",()=>assert.notEqual(cli([generic,"--claims",gp,"--format","report","--out",go]).status,0));
  test("input cannot be overwritten",()=>assert.notEqual(cli([generic,"--claims",gp,"--format","report","--out",generic]).status,0));
  test("generic stored results cannot be used as certificates",()=>assert.notEqual(cli([generic,"--claims",gp,"--format","report","--verify",verifier]).status,0));

  test("report fingerprints can be checked",()=>assert.equal(cli(["--check-fresh",go]).status,0));
  test("edited annotated copy is stale",()=>{fs.appendFileSync(go," ");assert.notEqual(cli(["--check-fresh",go]).status,0);});
  test("already annotated source is rejected",()=>{const s=render(source,report),r=structuredClone(report);r.source.sha256=hash(s);assert.throws(()=>render(s,r),/already contains/);});
  test("unsupported source is distinguished from failed proof search",()=>{
    const text="function gated(): null { for (;;) {} return null; }\n";
    const input=path.join(tmp,"gated.ts"),cp=path.join(tmp,"gated.json"),out=path.join(tmp,"gated.annotated.ts");
    fs.writeFileSync(input,text);
    fs.writeFileSync(cp,JSON.stringify([{file:input,functions:[{name:"gated",namePos:[9,14],params:[],retType:{top:false,atoms:[{a:"null"}]},envs:[],exprs:[]}]}]));
    const r=cli([input,"--claims",cp,"--verify",verifier,"--out",out]);assert.equal(r.status,0,r.stderr);
    assert.equal(JSON.parse(fs.readFileSync(out+".json")).results[0].status,"unsupported");
  });
  const real=fs.readFileSync(fileKey,"utf8"), claims=JSON.parse(fs.readFileSync(claimsPath));
  test("all real exported claims attach without changing syntax",()=>render(real,fromSkjs(real,fileKey,claims,"skjs")));
  const out=path.join(tmp,"real.annotated.ts");
  test("fresh independent verification is recorded",()=>{const r=cli([fileKey,"--claims",claimsPath,"--verify",verifier,"--out",out]);assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(out+".json"));assert(m.results.every(x=>x.status==="verified"));assert(m.results.every(x=>x.certificateSha256));assert.equal(m.verifierSha256,hash(fs.readFileSync(verifier)));assert.equal(m.source.sha256,hash(real));});
  test("false claim is not called refuted or verified",()=>{
    const c=structuredClone(claims), f=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="capturedRead");
    const parsed=spawnSync(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),fileKey,"--stateful"],{encoding:"utf8"});
    assert.equal(parsed.status,0,parsed.stderr);
    const body=JSON.parse(parsed.stdout).functions.find(f=>f.name==="capturedRead").body[1].init.body;
    const p=f.exprs.find(e=>e.pos[0]===body.pos[0] && e.pos[1]===body.pos[1]);assert(p);
    p.type={top:false,atoms:[{a:"booleanlit",v:"true"}]};
    const cp=path.join(tmp,"bad.json"),op=path.join(tmp,"bad.annotated.ts");fs.writeFileSync(cp,JSON.stringify(c));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json"));assert.equal(m.results[m.functions.findIndex(f=>f.name==="capturedRead")].status,"not-established");
  });
  console.log(`Annotated source: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
