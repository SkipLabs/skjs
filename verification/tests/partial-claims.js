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
} finally {fs.rmSync(temp,{recursive:true,force:true});}
console.log("Partial claims: default failure snapshots, unchanged diagnostics, recovery labels, gaps and independent verification passed.");
