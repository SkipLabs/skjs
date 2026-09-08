"use strict";
const fs=require("fs"),path=require("path"),os=require("os"),assert=require("assert");
const {spawnSync}=require("child_process");
const [claimsPath,file,partialPath,partialFile,recoveryPath,verifier,diagnostics]=process.argv.slice(2);
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"claim-export-tests-"));
const run=(exe,args)=>{const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});if(r.error||r.signal)throw r.error||Error(r.signal);return r;};
const script=path.resolve(__dirname,"../tools/export-source-claims.js");
let passed=0;
const test=(name,f)=>{f();passed++;console.log(`  ${name}: OK`);};
const convert=(source,claims,out,extra=[])=>run(process.execPath,[script,source,"--claims",claims,"--out",out,"--verifier",verifier,...extra]);
const parse=(source,ap)=>{const r=run(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),source,"--stateful"]);assert.equal(r.status,0,r.stderr);fs.writeFileSync(ap,r.stdout);};
try {
  const out=path.join(tmp,"closures.json"),ap=path.join(tmp,"closures.ast.json"),ep=path.join(tmp,"evidence.json");
  test("real SKJS closure claims convert",()=>{const r=convert(file,claimsPath,out);assert.equal(r.status,0,r.stderr);});
  const manifest=JSON.parse(fs.readFileSync(out+".conversion.json"));
  test("raw claims and omissions retained",()=>{assert.deepEqual(manifest.originalClaims,JSON.parse(fs.readFileSync(claimsPath)));assert(manifest.omissions.length>0);assert(manifest.omissions.every(x=>x.reason&&"raw" in x));});
  parse(file,ap);
  test("existing SKJS evidence checks against converted claims",()=>{
    const p=run(verifier,["--produce-stateful-source",ap,claimsPath,file,ep,"10"]);assert.equal(p.status,0,p.stderr);
    const c=run(verifier,["--check-source-claims",ap,out,file,ep]);assert.equal(c.status,0,c.stderr);
  });
  test("converted evidence checks against original SKJS claims",()=>{
    const p=run(verifier,["--produce-source-claims",ap,out,file,ep,"10"]);assert.equal(p.status,0,p.stderr);
    const c=run(verifier,["--check-stateful-source",ap,claimsPath,file,ep]);assert.equal(c.status,0,c.stderr);
  });
  test("existing output is not overwritten",()=>assert.notEqual(convert(file,claimsPath,out).status,0));
  const partial=path.join(tmp,"partial.json"),pa=path.join(tmp,"partial.ast.json");
  test("normal first-error snapshot converts without recovery",()=>{const r=convert(partialFile,partialPath,partial,["--diagnostics",diagnostics]);assert.equal(r.status,0,r.stderr);});
  const pm=JSON.parse(fs.readFileSync(partial+".conversion.json")),pc=JSON.parse(fs.readFileSync(partial));
  test("aborted collection and diagnostics preserved",()=>{assert(pm.functions.some(f=>f.collection.completion==="aborted"&&f.collection.mode==="normal"));assert.equal(pm.diagnostics,fs.readFileSync(diagnostics,"utf8"));assert.deepEqual(pm.originalClaims,JSON.parse(fs.readFileSync(partialPath)));});
  parse(partialFile,pa);
  test("partial conversion does not complete missing obligations",()=>assert.notEqual(run(verifier,["--produce-source-claims",pa,partial,partialFile,ep,"10"]).status,0));
  test("complete function in partial export still verifies",()=>{
    const ast=JSON.parse(fs.readFileSync(pa));ast.functions=ast.functions.filter(f=>f.name==="complete");
    const one=structuredClone(pc);one.functions=one.functions.filter(f=>f.name==="complete");
    const oa=path.join(tmp,"one.ast.json"),oc=path.join(tmp,"one.json");fs.writeFileSync(oa,JSON.stringify(ast));fs.writeFileSync(oc,JSON.stringify(one));
    const r=run(verifier,["--produce-source-claims",oa,oc,partialFile,ep,"10"]);assert.equal(r.status,0,r.stderr);
  });
  test("optional recovery provenance retained separately",()=>{const rp=path.join(tmp,"recovery.json"),r=convert(partialFile,recoveryPath,rp);assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(rp+".conversion.json"));assert(m.functions.some(f=>f.collection.quality==="recovery"));assert(!("collection" in JSON.parse(fs.readFileSync(rp)).functions[0]));});
  test("unsupported required type becomes a recorded gap",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath)),f=raw.find(f=>f.file===partialFile).functions.find(f=>f.name==="complete");
    f.exprs[0].type={unsupported:true};const cp=path.join(tmp,"unsupported.raw.json"),op=path.join(tmp,"unsupported.json");fs.writeFileSync(cp,JSON.stringify(raw));
    const r=convert(partialFile,cp,op);assert.equal(r.status,0,r.stderr);
    const d=JSON.parse(fs.readFileSync(op)),m=JSON.parse(fs.readFileSync(op+".conversion.json"));
    assert.equal(d.functions.find(f=>f.name==="complete").expressions.length,0);
    assert(m.omissions.some(o=>o.function==="complete"&&o.raw.unsupported===true));
    const oneAst=JSON.parse(fs.readFileSync(pa));oneAst.functions=oneAst.functions.filter(f=>f.name==="complete");d.functions=d.functions.filter(f=>f.name==="complete");
    const oa=path.join(tmp,"unavailable.ast.json"),oc=path.join(tmp,"unavailable-one.json");fs.writeFileSync(oa,JSON.stringify(oneAst));fs.writeFileSync(oc,JSON.stringify(d));
    assert.notEqual(run(verifier,["--produce-source-claims",oa,oc,partialFile,ep,"10"]).status,0);
  });
  test("unavailable signatures omit the function explicitly",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath));raw.find(f=>f.file===partialFile).functions.find(f=>f.name==="complete").retType={unsupported:true};
    const cp=path.join(tmp,"signature.raw.json"),op=path.join(tmp,"signature.json");fs.writeFileSync(cp,JSON.stringify(raw));const r=convert(partialFile,cp,op);assert.equal(r.status,0,r.stderr);
    assert(!JSON.parse(fs.readFileSync(op)).functions.some(f=>f.name==="complete"));
    assert(JSON.parse(fs.readFileSync(op+".conversion.json")).omissions.some(o=>o.reason.includes("signature")));
  });
  test("duplicate claims fail conversion rather than being merged",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath));const selected=raw.find(f=>f.file===partialFile);selected.functions.push(selected.functions[0]);const cp=path.join(tmp,"duplicate.json");fs.writeFileSync(cp,JSON.stringify(raw));assert.notEqual(convert(partialFile,cp,path.join(tmp,"duplicate-out.json")).status,0);
  });
  console.log(`Source claim export: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
