import fs from "node:fs";
import assert from "node:assert";
import os from "node:os";
import path from "node:path";
import { fromSkjs,render,coverage,verifySkjs,main } from "../tools/annotate-source.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import type { Manifest, Result } from "../report-viewer/types.ts";
import { must } from "./edits.mts";

/** The results a report states, which every check below is about. */
const results=(m: Manifest): Result[]=>must(m.results,"results");
const [normalPath,recoveryPath,file,verifier,diagnostics]=process.argv.slice(2);
const normal: SkjsClaims=JSON.parse(fs.readFileSync(normalPath, "utf8"));
const recovery: SkjsClaims=JSON.parse(fs.readFileSync(recoveryPath, "utf8"));
const source=fs.readFileSync(file,"utf8"), report=fromSkjs(source,file,normal,"skjs");
const get=(claims: SkjsClaims,name: string)=>functionOf(claims,file,name);
for(const name of ["annotationFailure","expressionFailure"]) {
  const f=get(normal,name);assert.equal(f.collection?.completion,"aborted");
  assert.equal(f.collection?.mode,"normal");assert.equal(f.collection?.quality,"unverified");
  assert(f.envs.length>0);assert(f.exprs.length>0);
  const r=get(recovery,name);assert.equal(r.collection?.mode,"keep-going");assert.equal(r.collection?.quality,name==="annotationFailure" ? "recovery" : "unverified");
}
assert.equal(get(normal,"complete").collection?.completion,"complete");
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
  const manifest: Manifest=JSON.parse(fs.readFileSync(out+".json", "utf8"));
  assert.equal(manifest.diagnostics,fs.readFileSync(diagnostics,"utf8"));assert.deepEqual(manifest.gaps,gaps);
  // Simulate a missing obligation in a valid function, without changing source
  // or asking SKJS to recover. A copied original claim supplies the repair.
  const incomplete=structuredClone(normal);
  get(incomplete,"complete").envs=[];
  const incompletePath=path.join(temp,"incomplete.json"), baseline=path.join(temp,"baseline.ts");
  fs.writeFileSync(incompletePath,JSON.stringify(incomplete));
  main([file,"--claims",incompletePath,"--verify",verifier,"--out",baseline]);
  const bm: Manifest=JSON.parse(fs.readFileSync(baseline+".json", "utf8"));
  const idx=bm.functions.findIndex((f) =>f.name==="complete");
  assert.equal(results(bm)[idx].status,"not-established");
  // A saved success is deliberately forged: comparison must not trust it.
  results(bm)[idx]={function:`f${idx}`,status:"verified"};fs.writeFileSync(baseline+".json",JSON.stringify(bm));
  const repaired=path.join(temp,"repaired.ts");
  main([file,"--claims",normalPath,"--producer","manual-repair","--baseline",baseline+".json","--verify",verifier,"--out",repaired]);
  const rm: Manifest=JSON.parse(fs.readFileSync(repaired+".json", "utf8"));
  assert.equal(results(rm)[idx].status,"verified");assert(results(rm)[idx].certificateSha256);
  const changes=must(rm.comparison,"a comparison").changes;
  assert(changes.some((c) =>c.function==="complete"&&c.kind==="entry"&&c.status==="added"));
  assert.equal(changes.length,1);
  main(["--check-fresh",repaired]);
  fs.appendFileSync(baseline+".json"," ");
  assert.throws(()=>main(["--check-fresh",repaired]),/stale/);
  const stillIncomplete=path.join(temp,"still-incomplete.ts");
  main([file,"--claims",incompletePath,"--baseline",baseline+".json","--verify",verifier,"--out",stillIncomplete]);
  const sm: Manifest=JSON.parse(fs.readFileSync(stillIncomplete+".json", "utf8"));
  assert.equal(results(sm)[idx].status,"not-established");
} finally {fs.rmSync(temp,{recursive:true,force:true});}
console.log("Partial claims: default failure snapshots, unchanged diagnostics, recovery labels, gaps and independent verification passed.");
