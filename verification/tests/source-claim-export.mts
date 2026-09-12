import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert";
import { spawnSync } from "node:child_process";
import { fromSourceClaims, verifySkjs } from "../tools/annotate-source.mts";
const __dirname = path.dirname(import.meta.filename);
const [claimsPath,file,partialPath,partialFile,recoveryPath,verifier,diagnostics]=process.argv.slice(2);
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),"claim-export-tests-"));
const run=(exe: string,args: string[])=>{const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;};
const script=path.resolve(__dirname,"../tools/export-source-claims.mts");
let passed=0;
const test=(name: string,f: any)=>{f();passed++;console.log(`  ${name}: OK`);};
const convert=(source: string,claims: any,out: any,extra: string[]=[])=>run(process.execPath,[script,source,"--claims",claims,"--out",out,"--verifier",verifier,...extra]);
const parse=(source: string,ap: any)=>{const r=run(process.execPath,[path.resolve(__dirname,"../tools/parse-source.mts"),source]);assert.equal(r.status,0,r.stderr);fs.writeFileSync(ap,r.stdout);};
try {
  const out=path.join(tmp,"closures.json"),ap=path.join(tmp,"closures.ast.json"),ep=path.join(tmp,"evidence.json");
  test("real SKJS closure claims convert",()=>{const r=convert(file,claimsPath,out);assert.equal(r.status,0,r.stderr);});
  const manifest=JSON.parse(fs.readFileSync(out+".conversion.json", "utf8"));
  test("raw claims and omissions retained",()=>{assert.deepEqual(manifest.originalClaims,JSON.parse(fs.readFileSync(claimsPath, "utf8")));assert(manifest.omissions.length>0);assert(manifest.omissions.every((x: any) =>x.reason&&"raw" in x));});
  parse(file,ap);
  test("existing SKJS evidence checks against converted claims",()=>{
    const p=run(verifier,["--produce-stateful-source",ap,claimsPath,file,ep,"10"]);assert.equal(p.status,0,p.stderr);
    const c=run(verifier,["--check-source-claims",ap,out,file,ep]);assert.equal(c.status,0,c.stderr);
  });
  test("converted evidence checks against original SKJS claims",()=>{
    const p=run(verifier,["--produce-source-claims",ap,out,file,ep,"10"]);assert.equal(p.status,0,p.stderr);
    const c=run(verifier,["--check-stateful-source",ap,claimsPath,file,ep]);assert.equal(c.status,0,c.stderr);
  });
  test("current contents export separately from the storage invariant",()=>{
    const raw=JSON.parse(fs.readFileSync(claimsPath, "utf8"));
    const selected=raw.find((f: any) =>f.file===file);
    let changed;
    for(const f of selected.functions) {
      const expr=f.exprs.find((e: any) =>e.type?.atoms?.length===1 && e.type.atoms[0].a==="record");
      if(!expr)continue;
      const field=expr.type.atoms[0].fields[0];
      field.write={top:false,atoms:[{a:"boolean"}]};
      field.read={top:false,atoms:[{a:"booleanlit",v:"true"}]};
      changed={name:f.name,pos:expr.pos};break;
    }
    assert(changed,"fixture must contain a cell expression");
    const cp=path.join(tmp,"current.raw.json"),op=path.join(tmp,"current.json");
    fs.writeFileSync(cp,JSON.stringify(raw));
    const r=convert(file,cp,op);assert.equal(r.status,0,r.stderr);
    const d=JSON.parse(fs.readFileSync(op, "utf8"));
    const point=d.functions.find((f: any) =>f.name===changed.name).expressions.find((e: any) =>JSON.stringify(e.pos)===JSON.stringify(changed.pos));
    assert.deepEqual(d.types[point.type[0]],[{refs:{first:[1,2],rest:[]}}]);assert.equal(point.type.length,1);assert.deepEqual(point.current,[1]);
    const omissions=JSON.parse(fs.readFileSync(op+".conversion.json", "utf8")).omissions;
    assert(!omissions.some((o: any) =>o.function===changed.name&&JSON.stringify(o.site.pos)===JSON.stringify(changed.pos)));
    const checked=run(verifier,["--produce-source-claims",ap,op,file,ep,"10"]);
    assert.equal(checked.status,0,checked.stderr);
    const rawCheck=run(verifier,["--check-stateful-source",ap,cp,file,ep]);
    assert.equal(rawCheck.status,0,rawCheck.stderr);
    const report=fromSourceClaims(fs.readFileSync(file,"utf8"),file,d,"candidate");
    const shown=report.functions.find(f=>f.name===changed.name)!.expressions.find(e=>JSON.stringify(e.pos)===JSON.stringify(changed.pos));
    assert(shown, "no claim at the changed point");
    assert(shown.type.includes(" = (true)"));
    assert.deepEqual(shown.raw,{type:point.type,current:[1]});
    const result=verifySkjs(file,fs.readFileSync(file,"utf8"),d,file,report,verifier,10,true)
      .results[report.functions.findIndex(f=>f.name===changed.name)];
    assert.equal(result.status,"verified");
    const check=()=>run(verifier,["--produce-source-claims",ap,op,file,ep,"10"]);
    point.current=[];fs.writeFileSync(op,JSON.stringify(d));
    assert.notEqual(run(verifier,["--check-source-claims",ap,op,file,ep]).status,0,"old evidence cannot erase an impossible observation");
    const empty=check();assert.notEqual(empty.status,0);
    assert(empty.stderr.includes("obligation-diagnostic:"),empty.stderr);
    point.current=point.type.slice();fs.writeFileSync(op,JSON.stringify(d));
    const invalid=check();assert.notEqual(invalid.status,0);
    assert(invalid.stderr.includes("invalid source claims"),invalid.stderr);
    delete point.current;fs.writeFileSync(op,JSON.stringify(d));
    assert.notEqual(check().status,0,"the format requires explicit assertion fields");
    point.current=[1];(d as any).status="verified";
    fs.writeFileSync(op,JSON.stringify(d));
    const extra=check();assert.notEqual(extra.status,0);
    assert(extra.stderr.includes("unknown fields"),extra.stderr);
  });
  test("existing output is not overwritten",()=>assert.notEqual(convert(file,claimsPath,out).status,0));
  const partial=path.join(tmp,"partial.json"),pa=path.join(tmp,"partial.ast.json");
  test("normal first-error snapshot converts without recovery",()=>{const r=convert(partialFile,partialPath,partial,["--diagnostics",diagnostics]);assert.equal(r.status,0,r.stderr);});
  const pm=JSON.parse(fs.readFileSync(partial+".conversion.json", "utf8")),pc=JSON.parse(fs.readFileSync(partial, "utf8"));
  test("aborted collection and diagnostics preserved",()=>{assert(pm.functions.some((f: any) =>f.collection.completion==="aborted"&&f.collection.mode==="normal"));assert.equal(pm.diagnostics,fs.readFileSync(diagnostics,"utf8"));assert.deepEqual(pm.originalClaims,JSON.parse(fs.readFileSync(partialPath, "utf8")));});
  parse(partialFile,pa);
  test("partial conversion does not complete missing obligations",()=>assert.notEqual(run(verifier,["--produce-source-claims",pa,partial,partialFile,ep,"10"]).status,0));
  test("complete function in partial export still verifies",()=>{
    const ast=JSON.parse(fs.readFileSync(pa, "utf8"));ast.functions=ast.functions.filter((f: any) =>f.name==="complete");
    const one=structuredClone(pc);one.functions=one.functions.filter((f: any) =>f.name==="complete");
    const oa=path.join(tmp,"one.ast.json"),oc=path.join(tmp,"one.json");fs.writeFileSync(oa,JSON.stringify(ast));fs.writeFileSync(oc,JSON.stringify(one));
    const r=run(verifier,["--produce-source-claims",oa,oc,partialFile,ep,"10"]);assert.equal(r.status,0,r.stderr);
  });
  test("optional recovery provenance retained separately",()=>{const rp=path.join(tmp,"recovery.json"),r=convert(partialFile,recoveryPath,rp);assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(rp+".conversion.json", "utf8"));assert(m.functions.some((f: any) =>f.collection.quality==="recovery"));assert(!("collection" in JSON.parse(fs.readFileSync(rp, "utf8")).functions[0]));});
  test("unsupported required type becomes a recorded gap",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath, "utf8")),f=raw.find((f: any) =>f.file===partialFile).functions.find((f: any) =>f.name==="complete");
    f.exprs[0].type={unsupported:true};const cp=path.join(tmp,"unsupported.raw.json"),op=path.join(tmp,"unsupported.json");fs.writeFileSync(cp,JSON.stringify(raw));
    const r=convert(partialFile,cp,op);assert.equal(r.status,0,r.stderr);
    const d=JSON.parse(fs.readFileSync(op, "utf8")),m=JSON.parse(fs.readFileSync(op+".conversion.json", "utf8"));
    assert.equal(d.functions.find((f: any) =>f.name==="complete").expressions.length,0);
    assert(m.omissions.some((o: any) =>o.function==="complete"&&o.raw.unsupported===true));
    const oneAst=JSON.parse(fs.readFileSync(pa, "utf8"));oneAst.functions=oneAst.functions.filter((f: any) =>f.name==="complete");d.functions=d.functions.filter((f: any) =>f.name==="complete");
    const oa=path.join(tmp,"unavailable.ast.json"),oc=path.join(tmp,"unavailable-one.json");fs.writeFileSync(oa,JSON.stringify(oneAst));fs.writeFileSync(oc,JSON.stringify(d));
    assert.notEqual(run(verifier,["--produce-source-claims",oa,oc,partialFile,ep,"10"]).status,0);
  });
  test("unavailable signatures omit the function explicitly",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath, "utf8"));raw.find((f: any) =>f.file===partialFile).functions.find((f: any) =>f.name==="complete").retType={unsupported:true};
    const cp=path.join(tmp,"signature.raw.json"),op=path.join(tmp,"signature.json");fs.writeFileSync(cp,JSON.stringify(raw));const r=convert(partialFile,cp,op);assert.equal(r.status,0,r.stderr);
    assert(!JSON.parse(fs.readFileSync(op, "utf8")).functions.some((f: any) =>f.name==="complete"));
    assert(JSON.parse(fs.readFileSync(op+".conversion.json", "utf8")).omissions.some((o: any) =>o.reason.includes("signature")));
  });
  test("duplicate claims fail conversion rather than being merged",()=>{
    const raw=JSON.parse(fs.readFileSync(partialPath, "utf8"));const selected=raw.find((f: any) =>f.file===partialFile);selected.functions.push(selected.functions[0]);const cp=path.join(tmp,"duplicate.json");fs.writeFileSync(cp,JSON.stringify(raw));assert.notEqual(convert(partialFile,cp,path.join(tmp,"duplicate-out.json")).status,0);
  });
  const annotate=path.resolve(__dirname,"../tools/annotate-source.mts");
  const report=(claims: any,out: any,extra: string[]=[])=>run(process.execPath,[annotate,partialFile,"--format","source-claims","--claims",claims,"--out",out,...extra]);
  const partialReport=path.join(tmp,"partial.annotated.ts");
  test("converted reports show original collection and fresh results",()=>{
    const r=report(partial,partialReport,["--conversion",partial+".conversion.json","--verify",verifier]);assert.equal(r.status,0,r.stderr);
    const text=fs.readFileSync(partialReport,"utf8"),m=JSON.parse(fs.readFileSync(partialReport+".json", "utf8"));
    assert(text.includes("original SKJS collection=aborted"));assert(text.includes("statement not visited"));assert(text.includes("expression entered without a type result"));
    assert.equal(m.conversion.diagnostics,pm.diagnostics);
    assert.equal(m.results[m.functions.findIndex((f: any) =>f.name==="complete")].status,"verified");
    assert.notEqual(m.results[m.functions.findIndex((f: any) =>f.name==="annotationFailure")].status,"verified");
  });
  test("converted recovery candidates stay visibly marked",()=>{
    const rp=path.join(tmp,"recovery.json"),out=path.join(tmp,"recovery.annotated.ts"),r=report(rp,out,["--conversion",rp+".conversion.json"]);
    assert.equal(r.status,0,r.stderr);const text=fs.readFileSync(out,"utf8");assert(text.includes("quality=recovery"));assert(text.includes("recovery claim"));
  });
  test("conversion omissions are distinct from unfinished expressions",()=>{
    const cp=path.join(tmp,"unsupported.json"),out=path.join(tmp,"omitted.annotated.ts"),r=report(cp,out,["--conversion",cp+".conversion.json"]);assert.equal(r.status,0,r.stderr);
    const m=JSON.parse(fs.readFileSync(out+".json", "utf8")),f=m.functions.find((f: any) =>f.name==="complete"),pos=f.collectionSnapshot.expressions[0].pos;
    assert(m.gaps.some((g: any) =>JSON.stringify(g.pos)===JSON.stringify(pos)&&g.status.includes("omitted during conversion")));
    assert(!m.gaps.some((g: any) =>JSON.stringify(g.pos)===JSON.stringify(pos)&&g.status==="expression entered without a type result"));
  });
  test("edited sidecar cannot inherit original collection labels",()=>{
    const edited=path.join(tmp,"edited.json"),d=structuredClone(pc);d.functions.find((f: any) =>f.name==="complete").entries=[];fs.writeFileSync(edited,JSON.stringify(d));
    const bad=report(edited,path.join(tmp,"bad-provenance.ts"),["--conversion",partial+".conversion.json"]);assert.notEqual(bad.status,0);assert(bad.stderr.includes("exact sidecar"));
    const out=path.join(tmp,"edited.annotated.ts"),good=report(edited,out,["--baseline",partialReport+".json","--verify",verifier]);assert.equal(good.status,0,good.stderr);
    const m=JSON.parse(fs.readFileSync(out+".json", "utf8"));assert(m.functions.every((f: any) =>!f.collection));assert.equal(m.comparison.changes.length,1);
    assert.equal(m.results[m.functions.findIndex((f: any) =>f.name==="complete")].status,"not-established");
  });
  test("conversion fingerprint participates in report freshness",()=>{
    const check=()=>run(process.execPath,[annotate,"--check-fresh",partialReport]);assert.equal(check().status,0);
    const cp=partial+".conversion.json",bytes=fs.readFileSync(cp);fs.appendFileSync(cp," ");assert.notEqual(check().status,0);fs.writeFileSync(cp,bytes);
  });
  test("conversion from another source is rejected",()=>{
    const m=structuredClone(pm);m.source.sha256="0".repeat(64);const cp=path.join(tmp,"stale-conversion.json");fs.writeFileSync(cp,JSON.stringify(m));
    const r=report(partial,path.join(tmp,"stale.ts"),["--conversion",cp]);assert.notEqual(r.status,0);assert(r.stderr.includes("identity mismatch"));
  });
  console.log(`Source claim export: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
