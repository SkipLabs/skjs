#!/usr/bin/env node
"use strict";
// Candidate conversion only. Type interpretation stays in the existing Lean decoder.
const fs=require("fs"),path=require("path"),os=require("os"),crypto=require("crypto");
const {spawnSync}=require("child_process");
const hash=x=>crypto.createHash("sha256").update(x).digest("hex");
function run(exe,args) {
  const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});
  if(r.error||r.signal)throw Error(`conversion tool failed: ${r.error?.message||r.signal}`);
  if(r.status!==0)throw Error((r.stderr||r.stdout||`tool exited ${r.status}`).trim());
  return r.stdout;
}
function main(args) {
  const sourcePath=args.shift(),opts={verifier:path.resolve(__dirname,"../lean/.lake/build/bin/verifier")};
  if(!sourcePath)throw Error("usage: export-source-claims.js source.ts --claims skjs.json [--out source-claims.json] [--diagnostics stderr.txt]");
  while(args.length) {
    const key=args.shift()?.replace(/^--/,"");
    if(!["claims","out","file-key","verifier","diagnostics"].includes(key)||!args.length)throw Error(`invalid option ${key}`);
    opts[key]=args.shift();
  }
  if(!opts.claims)throw Error("missing --claims");
  const output=opts.out||sourcePath.replace(/\.ts$/,"")+".source-claims.json",manifest=output+".conversion.json";
  if(fs.existsSync(output)||fs.existsSync(manifest))throw Error("output already exists; choose another --out path");
  const source=fs.readFileSync(sourcePath,"utf8"),raw=fs.readFileSync(opts.claims),originalClaims=JSON.parse(raw);
  const parser=path.resolve(__dirname,"parse-source.mts"),temp=fs.mkdtempSync(path.join(os.tmpdir(),"source-export-"));
  const diagnostics=opts.diagnostics?fs.readFileSync(opts.diagnostics,"utf8"):null;
  try {
    const ast=JSON.parse(run(process.execPath,[parser,sourcePath]));
    const file=opts["file-key"]||sourcePath;ast.file=file;
    if(ast.sourceSha256!==hash(source))throw Error("source changed during parsing");
    const ap=path.join(temp,"ast.json"),cp=path.join(temp,"claims.json");
    fs.writeFileSync(ap,JSON.stringify(ast));fs.writeFileSync(cp,raw);
    const converted=JSON.parse(run(opts.verifier,["--export-source-claims",ap,cp,file]));
    if(fs.readFileSync(sourcePath,"utf8")!==source||hash(fs.readFileSync(opts.claims))!==hash(raw))throw Error("input changed during conversion");
    const bytes=JSON.stringify(converted.claims,null,2)+"\n";
    const selected=originalClaims.find(f=>f.file===file);
    const provenance={version:1,kind:"skjs-source-claim-conversion",source:{file,sha256:hash(source)},
      sourcePath:path.resolve(sourcePath),claimsPath:path.resolve(opts.claims),claimsSha256:hash(raw),
      sidecarPath:path.resolve(output),sidecarSha256:hash(bytes),
      parserSha256:hash(fs.readFileSync(parser)),converterSha256:hash(fs.readFileSync(opts.verifier)),
      functions:selected.functions.map(f=>({name:f.name,namePos:f.namePos,...(f.collection?{collection:f.collection}:{})})),
      originalClaims,omissions:converted.omissions,
      ...(diagnostics!==null?{diagnostics,diagnosticsPath:path.resolve(opts.diagnostics),diagnosticsSha256:hash(diagnostics)}:{})};
    fs.writeFileSync(output,bytes,{flag:"wx"});
    try {fs.writeFileSync(manifest,JSON.stringify(provenance,null,2)+"\n",{flag:"wx"});}
    catch(e){fs.unlinkSync(output);throw e;}
    console.log(`Candidate sidecar: ${output}\nConversion manifest: ${manifest}\n${converted.omissions.length} omitted candidates/sites recorded. No verification performed.`);
  } finally {fs.rmSync(temp,{recursive:true,force:true});}
}
if(require.main===module)try {main(process.argv.slice(2));}catch(e){console.error(e.message);process.exitCode=1;}
module.exports={main};
