#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert";
import { spawnSync } from "node:child_process";
import { hash,render,fromSkjs,compareClaims,typeText } from "../tools/annotate-source.mts";
import { createRequire } from "node:module";
// Plain JavaScript modules; the reader loads these in a browser too.
const require = createRequire(import.meta.url);
const __dirname = path.dirname(import.meta.filename);
const [claimsPath,fileKey,verifier]=process.argv.slice(2);
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"annotated-tests-"));
let passed=0;
const test=(name: string,f: any)=>{f();passed++;console.log(`  ${name}: OK`);};
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
  test("stored generic statuses cannot establish verification",()=>{const r: any=structuredClone(report);r.results=[{status:"verified"}];assert(!render(source,r).includes("verification=verified"));});
  test("comparison ignores stored statuses and provenance changes",()=>{const r: any=structuredClone(report);r.results=[{status:"verified"}];r.producer="manual";assert.deepEqual(compareClaims(source,report,r).changes,[]);});
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
  test("unavailable reasons identify claims, ignore stale metadata, and preserve unknown codes",()=>{
    const raw: any=[{file:"test.ts",functions:[{name:"f",namePos:[ns,ns+1],
      params:[{name:"x",type:{unsupported:true}}],retType:{unsupported:true},
      envs:[{pos:[es-7,es+2],vars:[{name:"x",type:{unsupported:true}},{name:"y",type:{unsupported:true}}]}],
      exprs:[{pos:[es,es+1],type:{unsupported:true}}],
      unavailableTypes:[
        {kind:"parameter",binding:"x",reason:"unexpanded-type"},
        {kind:"result",reason:"unsupported-type"},
        {kind:"entry",pos:[es-7,es+2],binding:"x",reason:"multi-branch-object"},
        {kind:"entry",pos:[es-7,es+2],binding:"y",reason:"future-reason"},
        {kind:"expression",pos:[es,es+1],reason:"fuel-exhausted"}]}]}];
    // The probe always states some, and the assertions below are about how
    // many: a missing list is a failure, not an empty one.
    const get=()=>{const u=fromSkjs(source,"test.ts",raw,"skjs").functions[0]!.unavailableTypes;assert(u);return u;};
    assert.equal(get().length,5);
    assert.equal(get()[3]!.reason,"future-reason");
    const f=raw[0].functions[0];
    f.envs[0].vars[0].type={top:false,atoms:[{a:"boolean"}]};
    assert(!get().some(d=>d.kind==="entry"&&d.binding==="x"));
    f.unavailableTypes.push({...f.unavailableTypes[3],reason:"conflicting-reason"});
    assert(!get().some(d=>d.kind==="entry"&&d.binding==="y"));
    f.unavailableTypes.push(null,{kind:"expression",pos:null,reason:"bad"});
    assert.equal(get().length,3);
    delete f.unavailableTypes;
    assert.deepEqual(get(),[]);
  });
  const script=path.resolve(__dirname,"../tools/annotate-source.mts");
  const generic=path.join(tmp,"generic.ts"), gp=path.join(tmp,"generic.json"), go=path.join(tmp,"generic.annotated.ts");
  fs.writeFileSync(generic,source);fs.writeFileSync(gp,JSON.stringify(report));
  const cli=(args: string[]) =>{const r=spawnSync(process.execPath,[script,...args],{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;};
  test("generic claims CLI writes separate source and manifest",()=>{const r=cli([generic,"--claims",gp,"--format","report","--out",go]);assert.equal(r.status,0,r.stderr);assert.equal(fs.readFileSync(generic,"utf8"),source);const m=JSON.parse(fs.readFileSync(go+".json", "utf8"));assert.equal(m.annotatedSha256,hash(fs.readFileSync(go)));});
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
    assert.equal(JSON.parse(fs.readFileSync(out+".json", "utf8")).results[0].status,"unsupported");
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
    assert(edit && edit.includes("reason=claim-edit"));
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
    const r: any=structuredClone(report);
    r.functions[0].entries[0].bindings.push({name:"this",type:typeText({unsupported:true}),raw:{unsupported:true}});
    const entry=render(source,r).split("@verify-report").find(m=>m.includes("kind=entry"));
    assert(entry, "no entry annotation");
    assert(entry.includes("unsupported=this"),entry);
    assert(entry.includes("this: (unavailable)"),entry);
  });
  test("annotation ids resolve to manifest records",()=>{
    const r=cli([generic,"--claims",gp,"--format","report","--stdout","json"]);
    assert.equal(r.status,0,r.stderr);
    const {annotated,manifest}=JSON.parse(r.stdout);
    const ids=[...annotated.matchAll(/id=([a-z0-9]+);/g)].map(m=>m[1]);
    assert(ids.length>=3);
    const known=new Set([...manifest.functions.flatMap((f: any) =>[f.id,...f.entries.map((e: any) =>e.id),...f.expressions.map((e: any) =>e.id)]),
      ...manifest.gaps.map((g: any) =>g.id)]);
    for(const id of ids)assert(known.has(id),id);
  });
  test("stdout mode leaves no files behind",()=>{
    const before=fs.readdirSync(tmp);
    assert.equal(cli([generic,"--claims",gp,"--format","report","--stdout","json"]).status,0);
    assert.deepEqual(fs.readdirSync(tmp),before);
  });
  // Comments show claim types in surface syntax; the manifest keeps the exact
  // encoding. A shape the printer cannot name stays visible as its encoding.
  test("structured claims read as types in the comment, and stay exact in the manifest",()=>{
    const text="function cell(): boolean { return true; }\n";
    const ns=text.indexOf("cell"), ret=text.indexOf("true");
    const encoding={top:false,atoms:[{a:"record",fields:[{name:"value",optional:false,
      read:{top:false,atoms:[{a:"boolean"}]},write:{top:false,atoms:[{a:"boolean"}]}}],
      indexes:{string:"synthetic",number:"absent",symbol:"synthetic"},call:"absent",construct:"absent",array:"absent"}]};
    const exotic={top:false,atoms:[{a:"tuple",parts:[]}]};
    const input=path.join(tmp,"cell.ts"),cp=path.join(tmp,"cell.json"),out=path.join(tmp,"cell.annotated.ts");
    fs.writeFileSync(input,text);
    fs.writeFileSync(cp,JSON.stringify([{file:input,functions:[{name:"cell",namePos:[ns,ns+4],params:[],
      retType:{top:false,atoms:[{a:"boolean"}]},envs:[],
      exprs:[{pos:[ret,ret+4],type:encoding},{pos:[text.indexOf("return"),text.indexOf(";")+1],type:exotic}]}]}]));
    const r=cli([input,"--claims",cp,"--out",out]);assert.equal(r.status,0,r.stderr);
    const annotated=fs.readFileSync(out,"utf8");
    assert(annotated.includes("expr { value: boolean }"),annotated);
    assert(annotated.includes('"a":"tuple"'),"an unnameable shape keeps its encoding");
    const m=JSON.parse(fs.readFileSync(out+".json", "utf8"));
    assert.deepEqual(m.functions[0].expressions[0].raw,encoding);
    assert.deepEqual(m.functions[0].expressions[1].raw,exotic);
  });
  test("a type containing a comment terminator cannot end the comment",()=>{
    const text="function s(): boolean { return true; }\n";
    const ns=text.indexOf("s("), ret=text.indexOf("true");
    const encoding={top:false,atoms:[{a:"stringlit",v:"ends */ here"}]};
    const input=path.join(tmp,"esc.ts"),cp=path.join(tmp,"esc.json"),out=path.join(tmp,"esc.annotated.ts");
    fs.writeFileSync(input,text);
    fs.writeFileSync(cp,JSON.stringify([{file:input,functions:[{name:"s",namePos:[ns,ns+1],params:[],
      retType:{top:false,atoms:[{a:"boolean"}]},envs:[],exprs:[{pos:[ret,ret+4],type:encoding}]}]}]));
    const r=cli([input,"--claims",cp,"--out",out]);assert.equal(r.status,0,r.stderr);
    const annotated=fs.readFileSync(out,"utf8");
    assert(annotated.includes("ends *\\/ here"),annotated);
    assert(!/\*\/ here/.test(annotated),"the terminator must not survive unescaped");
    // The reader recovers the exact source from that comment.
    const {parseReport}=require("../report-viewer/model.js");
    assert.equal(parseReport(annotated).source,text);
  });
  const real=fs.readFileSync(fileKey,"utf8"), claims=JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  // Surface syntax is what a reader edits claims in, so it has to determine the
  // producer's encoding exactly. Check that on every type in a real export.
  test("every exported claim type survives printing and reading back",()=>{
    const {printType,parseType}=require("../tools/claim-types.js");
    const types: any[]=[];
    const walk=(f: any) =>{for(const e of f.exprs||[])types.push(e.type);
      for(const env of f.envs||[])for(const v of env.vars||[])types.push(v.type);
      for(const p of f.params||[])types.push(p.type); types.push(f.retType);};
    for(const file of claims)for(const f of file.functions)walk(f);
    const printable=types.filter(t=>t&&!t.unsupported&&printType(t).printable);
    assert(printable.length>50,`only ${printable.length} printable types`);
    for(const type of printable)
      assert.deepEqual(parseType(printType(type).text,type),type,printType(type).text);
  });
  test("all real exported claims attach without changing syntax",()=>render(real,fromSkjs(real,fileKey,claims,"skjs")));
  const out=path.join(tmp,"real.annotated.ts");
  test("fresh independent verification is recorded",()=>{const r=cli([fileKey,"--claims",claimsPath,"--verify",verifier,"--out",out]);assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(out+".json", "utf8"));assert(m.results.every((x: any) =>x.status==="verified"));assert(m.results.every((x: any) =>x.certificateSha256));assert.equal(m.verifierSha256,hash(fs.readFileSync(verifier)));assert.equal(m.source.sha256,hash(real));});
  // A claim the extractor needed and did not find is a different finding from a
  // proof search that failed, and the report must say which one happened.
  test("an absent required claim is located as a missing claim",()=>{
    const c=structuredClone(claims), f=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="capturedRead");
    const parsed=spawnSync(process.execPath,[path.resolve(__dirname,"../tools/parse-source.mts"),fileKey],{encoding:"utf8"});
    assert.equal(parsed.status,0,parsed.stderr);
    const body=JSON.parse(parsed.stdout).functions.find((f: any) =>f.name==="capturedRead").body[1].init.body;
    const removed=f.exprs.find((e: any) =>e.pos[0]===body.pos[0] && e.pos[1]===body.pos[1]);assert(removed);
    f.exprs=f.exprs.filter((e: any) =>e!==removed);
    const cp=path.join(tmp,"absent.json"),op=path.join(tmp,"absent.annotated.ts");fs.writeFileSync(cp,JSON.stringify(c));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json", "utf8"));
    const result=m.results[m.functions.findIndex((f: any) =>f.name==="capturedRead")];
    assert.equal(result.status,"not-established");
    assert.deepEqual(result.location,{kind:"missing-expression-claim",pos:removed.pos});
  });
  test("an absent environment claim names the statement, and a missing binding names itself",()=>{
    const c=structuredClone(claims), f=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="capturedRead");
    const dropped=f.envs[f.envs.length-1];assert(dropped);
    const withoutEnv=structuredClone(c);
    const g=withoutEnv.find((x: any) =>x.file===fileKey).functions.find((x: any) =>x.name==="capturedRead");
    g.envs=g.envs.filter((e: any) =>e.pos[0]!==dropped.pos[0]);
    const cp=path.join(tmp,"noenv.json"),op=path.join(tmp,"noenv.annotated.ts");
    fs.writeFileSync(cp,JSON.stringify(withoutEnv));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json", "utf8"));
    const result=m.results[m.functions.findIndex((x: any) =>x.name==="capturedRead")];
    assert.equal(result.location.kind,"missing-environment-claim");
    assert.equal(result.location.start,dropped.pos[0]);
    const withoutBinding=structuredClone(c);
    const h=withoutBinding.find((x: any) =>x.file===fileKey).functions.find((x: any) =>x.name==="capturedRead");
    const target=h.envs.find((e: any) =>e.vars.some((v: any) =>v.name!=="this"));assert(target);
    const name=target.vars.find((v: any) =>v.name!=="this").name;
    target.vars=target.vars.filter((v: any) =>v.name!==name);
    const bp=path.join(tmp,"nobinding.json"),bo=path.join(tmp,"nobinding.annotated.ts");
    fs.writeFileSync(bp,JSON.stringify(withoutBinding));
    const rb=cli([fileKey,"--claims",bp,"--verify",verifier,"--out",bo]);assert.equal(rb.status,0,rb.stderr);
    const mb=JSON.parse(fs.readFileSync(bo+".json", "utf8"));
    const rr=mb.results[mb.functions.findIndex((x: any) =>x.name==="capturedRead")];
    if(rr.location?.kind==="missing-environment-claim")assert.equal(rr.location.binding,name);
    else assert.equal(rr.status,"not-established");
  });
  test("a fragment limitation reported without a span is still located as one",()=>{
    const text="function outside(x: string): string { return x; }\n";
    const input=path.join(tmp,"outside.ts"),cp=path.join(tmp,"outside.json"),out=path.join(tmp,"outside.annotated.ts");
    fs.writeFileSync(input,text);
    const ns=text.indexOf("outside");
    fs.writeFileSync(cp,JSON.stringify([{file:input,functions:[{name:"outside",namePos:[ns,ns+7],
      params:[{name:"x",type:{top:false,atoms:[{a:"string"}]}}],retType:{top:false,atoms:[{a:"string"}]},envs:[],exprs:[]}]}]));
    const r=cli([input,"--claims",cp,"--verify",verifier,"--out",out]);assert.equal(r.status,0,r.stderr);
    const result=JSON.parse(fs.readFileSync(out+".json", "utf8")).results[0];
    if(/outside the .*slice/.test(result.detail||""))assert.deepEqual(result.location,{kind:"source-limitation"});
    else assert.equal(result.status,"unsupported");
  });
  test("false claim is not called refuted or verified",()=>{
    const c=structuredClone(claims), f=c.find((f: any) =>f.file===fileKey).functions.find((f: any) =>f.name==="capturedRead");
    const parsed=spawnSync(process.execPath,[path.resolve(__dirname,"../tools/parse-source.mts"),fileKey],{encoding:"utf8"});
    assert.equal(parsed.status,0,parsed.stderr);
    const body=JSON.parse(parsed.stdout).functions.find((f: any) =>f.name==="capturedRead").body[1].init.body;
    const p=f.exprs.find((e: any) =>e.pos[0]===body.pos[0] && e.pos[1]===body.pos[1]);assert(p);
    p.type={top:false,atoms:[{a:"booleanlit",v:"true"}]};
    const cp=path.join(tmp,"bad.json"),op=path.join(tmp,"bad.annotated.ts");fs.writeFileSync(cp,JSON.stringify(c));
    const r=cli([fileKey,"--claims",cp,"--verify",verifier,"--out",op]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(op+".json", "utf8"));assert.equal(m.results[m.functions.findIndex((f: any) =>f.name==="capturedRead")].status,"not-established");
  });
  console.log(`Annotated source: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
