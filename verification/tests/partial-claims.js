"use strict";
const fs=require("fs"),assert=require("assert"),os=require("os"),path=require("path");
const {fromSkjs,render,coverage,verifySkjs,main}=require("../tools/annotate-source.js");
const [normalPath,recoveryPath,file,verifier,diagnostics]=process.argv.slice(2);
const normal=JSON.parse(fs.readFileSync(normalPath)),recovery=JSON.parse(fs.readFileSync(recoveryPath));
const source=fs.readFileSync(file,"utf8"), report=fromSkjs(source,file,normal,"skjs");
const get=(claims,name)=>claims.find(f=>f.file===file).functions.find(f=>f.name===name);
for(const name of ["annotationFailure","expressionFailure"]) {
  const f=get(normal,name);assert.equal(f.collection.completion,"aborted");
  assert.equal(f.collection.mode,"normal");assert.equal(f.collection.quality,"unverified");
  assert(f.envs.length>0);assert(f.exprs.length>0);
  const r=get(recovery,name);assert.equal(r.collection.mode,"keep-going");assert.equal(r.collection.quality,name==="annotationFailure" ? "recovery" : "unverified");
}
assert.equal(get(normal,"complete").collection.completion,"complete");
const gaps=coverage(source,report);
assert(gaps.some(g=>g.status==="statement not visited"));
assert(gaps.some(g=>g.status==="expression entered without a type result"));
assert(render(source,report).includes("collection=aborted"));
assert(render(source,fromSkjs(source,file,recovery,"skjs")).includes("recovery claim"));
const verified=verifySkjs(file,source,normal,file,report,verifier,10);
assert.equal(verified.results[report.functions.findIndex(f=>f.name==="complete")].status,"verified");
for(const name of ["annotationFailure","expressionFailure"])assert.notEqual(verified.results[report.functions.findIndex(f=>f.name===name)].status,"verified");
const temp=fs.mkdtempSync(path.join(os.tmpdir(),"partial-report-"));
try {
  const out=path.join(temp,"report.ts");main([file,"--claims",normalPath,"--diagnostics",diagnostics,"--out",out]);
  const manifest=JSON.parse(fs.readFileSync(out+".json"));
  assert.equal(manifest.diagnostics,fs.readFileSync(diagnostics,"utf8"));assert.deepEqual(manifest.gaps,gaps);
  // Simulate a missing obligation in a valid function, without changing source
  // or asking SKJS to recover. A copied original claim supplies the repair.
  const incomplete=structuredClone(normal);
  get(incomplete,"complete").envs=[];
  const incompletePath=path.join(temp,"incomplete.json"), baseline=path.join(temp,"baseline.ts");
  fs.writeFileSync(incompletePath,JSON.stringify(incomplete));
  main([file,"--claims",incompletePath,"--verify",verifier,"--out",baseline]);
  const bm=JSON.parse(fs.readFileSync(baseline+".json"));
  const idx=bm.functions.findIndex(f=>f.name==="complete");
  assert.equal(bm.results[idx].status,"not-established");
  // A saved success is deliberately forged: comparison must not trust it.
  bm.results[idx]={status:"verified"};fs.writeFileSync(baseline+".json",JSON.stringify(bm));
  const repaired=path.join(temp,"repaired.ts");
  main([file,"--claims",normalPath,"--producer","manual-repair","--baseline",baseline+".json","--verify",verifier,"--out",repaired]);
  const rm=JSON.parse(fs.readFileSync(repaired+".json"));
  assert.equal(rm.results[idx].status,"verified");assert(rm.results[idx].certificateSha256);
  assert(rm.comparison.changes.some(c=>c.function==="complete"&&c.kind==="entry"&&c.status==="added"));
  assert.equal(rm.comparison.changes.length,1);
  main(["--check-fresh",repaired]);
  fs.appendFileSync(baseline+".json"," ");
  assert.throws(()=>main(["--check-fresh",repaired]),/stale/);
  const stillIncomplete=path.join(temp,"still-incomplete.ts");
  main([file,"--claims",incompletePath,"--baseline",baseline+".json","--verify",verifier,"--out",stillIncomplete]);
  assert.equal(JSON.parse(fs.readFileSync(stillIncomplete+".json")).results[idx].status,"not-established");
} finally {fs.rmSync(temp,{recursive:true,force:true});}
console.log("Partial claims: default failure snapshots, unchanged diagnostics, recovery labels, gaps and independent verification passed.");
