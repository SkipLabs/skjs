#!/usr/bin/env node
// Candidate conversion only. Type interpretation stays in the existing Lean decoder.
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";
import type { SkjsClaims, SkjsCollection } from "./skjs-claims.mts";
import type { Span } from "./span.mts";

/**
 * The manifest this tool writes beside a converted sidecar: where the
 * conversion came from, what it refused, and the producer's own claims kept
 * verbatim. Nothing here is evidence — it records that a conversion ran.
 */
export interface ConversionManifest {
  kind: "skjs-source-claim-conversion";
  source: { file: string; sha256: string };
  sourcePath: string;
  claimsPath: string;
  claimsSha256: string;
  sidecarPath: string;
  sidecarSha256: string;
  converterSha256: string;
  /** The functions the producer spoke about, with its own progress record. */
  functions: { name: string; namePos: Span; collection?: SkjsCollection }[];
  originalClaims: SkjsClaims;
  /** What the conversion refused, with the producer's own encoding beside it. */
  omissions: {
    function: string;
    namePos: Span;
    /** Where the refusal is, as the converter names it: an expression by its
     * span, an entry by the statement it begins, or the word for a whole
     * function or a result, which have no site of their own. */
    site?: { kind: string; pos?: Span; name?: string; start?: number } | string;
    reason: string;
    raw?: unknown;
  }[];
  /** The producer's own stderr, where the caller supplied it. */
  diagnostics?: string;
  diagnosticsPath?: string;
  diagnosticsSha256?: string;
}

const __dirname = path.dirname(new URL(import.meta.url).pathname);
const hash = (x: crypto.BinaryLike) =>
  crypto.createHash("sha256").update(x).digest("hex");
function run(exe: string, args: string[]): string {
  const r=spawnSync(exe,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});
  if(r.error||r.signal)throw Error(`conversion tool failed: ${r.error?.message||r.signal}`);
  if(r.status!==0)throw Error((r.stderr||r.stdout||`tool exited ${r.status}`).trim());
  return r.stdout;
}
export function main(args: string[]) {
  const sourcePath=args.shift();
  // Every switch accepted below lands here, so the record says so once rather
  // than growing a property at a time.
  const opts = {verifier:path.resolve(__dirname,"../lean/.lake/build/bin/verifier")} as {
    verifier:string, claims?:string, out?:string, "file-key"?:string, diagnostics?:string,
  };
  if(!sourcePath)throw Error("usage: export-source-claims.mts source.ts --claims skjs.json [--out source-claims.json] [--diagnostics stderr.txt]");
  while(args.length) {
    const key=args.shift()?.replace(/^--/,"");
    if(!key||!["claims","out","file-key","verifier","diagnostics"].includes(key)||!args.length)throw Error(`invalid option ${key}`);
    (opts as Record<string,string|undefined>)[key]=args.shift();
  }
  if(!opts.claims)throw Error("missing --claims");
  const output=opts.out||sourcePath.replace(/\.ts$/,"")+".source-claims.json",manifest=output+".conversion.json";
  if(fs.existsSync(output)||fs.existsSync(manifest))throw Error("output already exists; choose another --out path");
  const source=fs.readFileSync(sourcePath,"utf8"),raw=fs.readFileSync(opts.claims,"utf8"),originalClaims: SkjsClaims=JSON.parse(raw);
  const parser=path.resolve(__dirname,"fragment-parse.mts"),temp=fs.mkdtempSync(path.join(os.tmpdir(),"source-export-"));
  const diagnostics=opts.diagnostics?fs.readFileSync(opts.diagnostics,"utf8"):null;
  try {
    const file=opts["file-key"]||sourcePath;
    let ast;
    try { ast=JSON.parse(run(process.execPath,[parser,sourcePath])); }
    catch(error) {
      if(!String((error as Error).message).startsWith("gate:"))throw error;
    }
    const cp=path.join(temp,"claims.json");fs.writeFileSync(cp,raw);
    let converted;
    if(ast) {
      ast.file=file;
      if(ast.sourceSha256!==hash(source))throw Error("source changed during parsing");
      const ap=path.join(temp,"ast.json");fs.writeFileSync(ap,JSON.stringify(ast));
      converted=JSON.parse(run(opts.verifier,["--export-source-claims",ap,cp,file]));
    } else {
      converted=JSON.parse(run(opts.verifier,["--import-skjs-claims",cp,file,hash(source)]));
    }
    if(fs.readFileSync(sourcePath,"utf8")!==source||hash(fs.readFileSync(opts.claims,"utf8"))!==hash(raw))throw Error("input changed during conversion");
    const bytes=JSON.stringify(converted.claims,null,2)+"\n";
    const selected=originalClaims.find(f=>f.file===file);
    if(!selected)throw Error(`the producer said nothing about ${file}`);
    const provenance={kind:"skjs-source-claim-conversion",source:{file,sha256:hash(source)},
      sourcePath:path.resolve(sourcePath),claimsPath:path.resolve(opts.claims),claimsSha256:hash(raw),
      sidecarPath:path.resolve(output),sidecarSha256:hash(bytes),
      converterSha256:hash(fs.readFileSync(opts.verifier)),
      functions:selected.functions.map(f=>({name:f.name,namePos:f.namePos,...(f.collection?{collection:f.collection}:{})})),
      originalClaims,omissions:converted.omissions,
      ...(diagnostics!==null?{diagnostics,diagnosticsPath:path.resolve(opts.diagnostics!),diagnosticsSha256:hash(diagnostics)}:{})};
    fs.writeFileSync(output,bytes,{flag:"wx"});
    try {fs.writeFileSync(manifest,JSON.stringify(provenance,null,2)+"\n",{flag:"wx"});}
    catch(e){fs.unlinkSync(output);throw e;}
    console.log(`Candidate sidecar: ${output}\nConversion manifest: ${manifest}\n${converted.omissions.length} omitted candidates/sites recorded. No verification performed.`);
  } finally {fs.rmSync(temp,{recursive:true,force:true});}
}
if(process.argv[1] && import.meta.filename===path.resolve(process.argv[1]))
  try {main(process.argv.slice(2));}catch(e){console.error((e as Error).message);process.exitCode=1;}
