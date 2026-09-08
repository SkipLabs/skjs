#!/usr/bin/env node
"use strict";
const fs=require("fs"),path=require("path"),os=require("os"),assert=require("assert");
const {spawnSync}=require("child_process");
const {hash,render,fromSkjs,compareClaims,typeText}=require("../tools/annotate-source.js");
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
  test("every claim annotation carries its kind and a manifest id",()=>{
    const marks=render(source,report).split("@verify-report").slice(2);
    assert(marks.length>=2);
    for(const m of marks)assert(/^ kind=(entry|expression|function|gap); (reason=[a-z0-9-]+; )?id=[a-z0-9]+; /.test(m),m.slice(0,60));
  });
  test("gap reason is a slug that survives rewording the prose",()=>{
    const r=structuredClone(report);r.functions[0].expressions=[];
    const marks=render(source,r).split("@verify-report").slice(2);
    assert(!marks.some(m=>m.includes("reason=")));
    const changes=compareClaims(source,report,r).changes;
    const edit=render(source,r,null,{claimChanges:changes}).split("@verify-report").find(m=>m.includes("claim edit:"));
    assert(edit.includes("reason=claim-edit"));
  });
  test("literal types are displayed as literals, not as encodings",()=>{
    const r=structuredClone(report);
    r.functions[0].expressions[0].type=typeText({top:false,atoms:[{a:"stringlit",v:"a"},{a:"numberlit",v:"3"},{a:"null"}]});
    const text=render(source,r);
    assert(text.includes('expr "a" | 3 | null'),text);
  });
  test("an unrecognised type payload is preserved rather than abbreviated away",()=>{
    const t={top:false,atoms:[{a:"objectlit",v:{x:1}}]};
    assert.equal(typeText(t),JSON.stringify(t));
  });
  test("bindings without a decoded type are named in the annotation",()=>{
    const r=structuredClone(report);
    r.functions[0].entries[0].bindings.push({name:"this",type:typeText({unsupported:true}),raw:{unsupported:true}});
    const entry=render(source,r).split("@verify-report").find(m=>m.includes("kind=entry"));
    assert(entry.includes("unsupported=this"),entry);
    assert(entry.includes("this: (unavailable)"),entry);
  });
  test("annotation ids resolve to manifest records",()=>{
    const r=cli([generic,"--claims",gp,"--format","report","--stdout","json"]);
    assert.equal(r.status,0,r.stderr);
    const {annotated,manifest}=JSON.parse(r.stdout);
    const ids=[...annotated.matchAll(/id=([a-z0-9]+);/g)].map(m=>m[1]);
    assert(ids.length>=3);
    const known=new Set([...manifest.functions.flatMap(f=>[f.id,...f.entries.map(e=>e.id),...f.expressions.map(e=>e.id)]),
      ...manifest.gaps.map(g=>g.id)]);
    for(const id of ids)assert(known.has(id),id);
  });
  test("stdout mode leaves no files behind",()=>{
    const before=fs.readdirSync(tmp);
    assert.equal(cli([generic,"--claims",gp,"--format","report","--stdout","json"]).status,0);
    assert.deepEqual(fs.readdirSync(tmp),before);
  });
  const real=fs.readFileSync(fileKey,"utf8"), claims=JSON.parse(fs.readFileSync(claimsPath));
  test("all real exported claims attach without changing syntax",()=>render(real,fromSkjs(real,fileKey,claims,"skjs")));
  const out=path.join(tmp,"real.annotated.ts");
  test("fresh independent verification is recorded",()=>{const r=cli([fileKey,"--claims",claimsPath,"--verify",verifier,"--out",out]);assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(out+".json"));assert(m.results.every(x=>x.status==="verified"));assert(m.results.every(x=>x.certificateSha256));assert.equal(m.verifierSha256,hash(fs.readFileSync(verifier)));assert.equal(m.source.sha256,hash(real));});
  // A claim the extractor needed and did not find is a different finding from a
  // proof search that failed, and the report must say which one happened.
  test("an absent required claim is located as a missing claim",()=>{
    const c=structuredClone(claims), f=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="capturedRead");
    const parsed=spawnSync(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),fileKey],{encoding:"utf8"});
    assert.equal(parsed.status,0,parsed.stderr);
    const body=JSON.parse(parsed.stdout).functions.find(f=>f.name==="capturedRead").body[1].init.body;
    const removed=f.exprs.find(e=>e.pos[0]===body.pos[0] && e.pos[1]===body.pos[1]);assert(removed);
    f.exprs=f.exprs.filter(e=>e!==removed);
    const cp=path.join(tmp,"absent.json"),op=path.join(tmp,"absent.annotated.ts");fs.writeFileSync(cp,JSON.stringify(c));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json"));
    const result=m.results[m.functions.findIndex(f=>f.name==="capturedRead")];
    assert.equal(result.status,"not-established");
    assert.deepEqual(result.location,{kind:"missing-expression-claim",pos:removed.pos});
  });
  test("an absent environment claim names the statement, and a missing binding names itself",()=>{
    const c=structuredClone(claims), f=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="capturedRead");
    const dropped=f.envs[f.envs.length-1];assert(dropped);
    const withoutEnv=structuredClone(c);
    const g=withoutEnv.find(x=>x.file===fileKey).functions.find(x=>x.name==="capturedRead");
    g.envs=g.envs.filter(e=>e.pos[0]!==dropped.pos[0]);
    const cp=path.join(tmp,"noenv.json"),op=path.join(tmp,"noenv.annotated.ts");
    fs.writeFileSync(cp,JSON.stringify(withoutEnv));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json"));
    const result=m.results[m.functions.findIndex(x=>x.name==="capturedRead")];
    assert.equal(result.location.kind,"missing-environment-claim");
    assert.equal(result.location.start,dropped.pos[0]);
    const withoutBinding=structuredClone(c);
    const h=withoutBinding.find(x=>x.file===fileKey).functions.find(x=>x.name==="capturedRead");
    const target=h.envs.find(e=>e.vars.some(v=>v.name!=="this"));assert(target);
    const name=target.vars.find(v=>v.name!=="this").name;
    target.vars=target.vars.filter(v=>v.name!==name);
    const bp=path.join(tmp,"nobinding.json"),bo=path.join(tmp,"nobinding.annotated.ts");
    fs.writeFileSync(bp,JSON.stringify(withoutBinding));
    const rb=cli([fileKey,"--claims",bp,"--verify",verifier,"--out",bo]);assert.equal(rb.status,0,rb.stderr);
    const mb=JSON.parse(fs.readFileSync(bo+".json"));
    const rr=mb.results[mb.functions.findIndex(x=>x.name==="capturedRead")];
    if(rr.location?.kind==="missing-environment-claim")assert.equal(rr.location.binding,name);
    else assert.equal(rr.status,"not-established");
  });
  test("false claim is not called refuted or verified",()=>{
    const c=structuredClone(claims), f=c.find(f=>f.file===fileKey).functions.find(f=>f.name==="capturedRead");
    const parsed=spawnSync(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),fileKey],{encoding:"utf8"});
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
