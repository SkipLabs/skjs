#!/usr/bin/env node

// Display-only reports. These comments are never certificate input.
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";
import * as ts from "typescript/unstable/ast";
import { createScanner } from "typescript/unstable/ast/scanner";
import { createRequire } from "node:module";
// The source annotation encoding has exactly one implementation; a second
// would be a second opinion about what a source type means.
import * as parseSource from "./parse-source.mts";
const __dirname = path.dirname(new URL(import.meta.url).pathname);
// The display helpers beside this file are plain JavaScript modules.
const require = createRequire(import.meta.url);
const hash = data => crypto.createHash("sha256").update(data).digest("hex");
const clone = x => JSON.parse(JSON.stringify(x));
// Escapes what could end or break the comment; a quote cannot, and a string
// literal reads better unescaped. A backslash stays doubled, so the text is
// still decodable: "\\" is one backslash, '"' is one quote.
const safeText = x => JSON.stringify(String(x)).slice(1,-1).replace(/\\"/g,'"').replace(/\*\//g,"*\\/").replace(/[\u2028\u2029]/g,c=>c==="\u2028"?"\\u2028":"\\u2029");
// Every annotation carries its kind, a stable id joining it to the manifest, and,
// for a gap, the reason as a slug. The prose stays: these comments are read by
// people as well as by tools, and a reworded sentence must not break a reader.
const reasons = {
  "statement not visited":"statement-not-visited",
  "expression entered without a type result":"expression-without-type",
  "claims unavailable; verification not established":"claims-unavailable"};
const reasonSlug = detail => reasons[detail] ||
  (/^claim edit:/.test(detail) ? "claim-edit"
   : detail.toLowerCase().replace(/[^a-z0-9]+/g,"-").replace(/^-|-$/g,"").split("-").slice(0,4).join("-"));
function fields(x) {
  const parts=["kind="+x.kind];
  if(x.kind === "gap")parts.push("reason="+reasonSlug(x.detail));
  if(x.id)parts.push("id="+x.id);
  if(x.unsupported && x.unsupported.length)parts.push("unsupported="+x.unsupported.join("+"));
  return parts.join("; ")+"; ";
}
function comment(x) {
  if(x.kind === "report") {
    const lines=["Display-only claim report; not certificate input.",
      "annotation-fields=kind,reason,id,unsupported",`producer=${x.producer}`,
      `source=${x.source.file}`,`source-sha256=${x.source.sha256}`,
      ...Object.entries(x).filter(([k])=>k.endsWith("Sha256")).map(([k,v])=>`${k}=${v}`),
      ...(x.claimChanges ? [`Claim edits against baseline: ${x.claimChanges.length}; before/after values are in the manifest.`] : []),
      ...(x.conversionOmissions ? [`Conversion omissions: ${x.conversionOmissions.length}; original payloads and reasons are in the manifest.`] : []),
      "Function results cover modeled obligations, not every exported claim.",
      "Original spans are before annotation. Full details are in the companion JSON manifest."];
    return "/* @verify-report\n * "+lines.map(safeText).join("\n * ")+"\n */\n";
  }
  let text;
  if(x.kind === "function") {
    const signature=x.signature ? `; claimed (${x.signature.params.map(p=>`${p.name}: ${typeText(p.type)}`).join(", ")}) => ${typeText(x.signature.retType)}` : "";
    text=`function ${x.name}; producer=${x.producer}${signature}; verification=${x.verification.status}`;
    if(x.collection)text+=`; ${x.collectionSource||""}collection=${x.collection.completion}; quality=${x.collection.quality}; mode=${x.collection.mode}`;
    if(x.verification.detail)text+=`; ${x.verification.detail}`;
  } else if(x.kind === "entry") {
    text=`entry { ${x.bindings.map(b=>`${b.name}: ${b.type}`).join(", ")} }`;
  } else if(x.kind === "gap")text=x.detail;
  else text=`expr ${x.type}`;
  if(x.quality === "recovery")text+="; recovery claim";
  if(x.originalSpan)text+=` @${x.originalSpan[0]}:${x.originalSpan[1]}`;
  return `/* @verify-report ${safeText(fields(x)+text)} */ `;
}

// The same printer the reader uses, so a comment and a panel say the same thing.
// The manifest keeps the producer's encoding; this is a readable view of it.
const {printType}=require("./claim-types.js");
function typeText(t) {
  if(typeof t==="string")return t;
  // A binding the producer could not decode has no claimed type. Name the
  // absence instead of printing an encoding that reads like a type; the exact
  // payload stays in the manifest, joined by the annotation id.
  if(t && t.unsupported === true && Object.keys(t).length === 1)return "(unavailable)";
  // Surface syntax where the printer can name the type; the exact encoding
  // otherwise, so a shape it does not know is never quietly hidden.
  const printed=printType(t);
  if(printed.printable)return printed.text;
  if(t && t.top === false && Object.keys(t).sort().join() === "atoms,top" && Array.isArray(t.atoms)) {
    const names=t.atoms.map(a=> {
      if(Object.keys(a).join() === "a" && ["null","boolean","string","number","undefined"].includes(a.a))return a.a;
      if(Object.keys(a).sort().join() !== "a,v")return null;
      // Literal types are displayed as the literal they are. Nothing is dropped:
      // the exact payload stays in the manifest, joined by the annotation id.
      if(a.a === "booleanlit" && ["true","false"].includes(a.v))return a.v;
      if(a.a === "stringlit" && typeof a.v === "string")return JSON.stringify(a.v);
      if((a.a === "numberlit" || a.a === "numlit") && Number.isFinite(Number(a.v)))return String(a.v);
      return null;
    });
    if(names.every(x=>x!==null))return names.length ? names.join(" | ") : "never";
  }
  return JSON.stringify(t);
}

// Advisory exporter metadata is bound to an exact claim address. Ignore stale,
// malformed and ambiguous entries; none can turn an unavailable type into evidence.
function unavailableTypes(f) {
  const missing=t=>t && t.unsupported===true && Object.keys(t).length===1;
  const key=d=>JSON.stringify([d.kind,d.pos,d.binding]);
  const claims=new Map(), reasons=new Map();
  const add=(d,t)=>{if(missing(t))claims.set(key(d),(claims.get(key(d))||0)+1);};
  for(const p of f.params)add({kind:"parameter",binding:p.name},p.type);
  add({kind:"result"},f.retType);
  for(const e of f.envs)for(const v of e.vars)add({kind:"entry",pos:e.pos,binding:v.name},v.type);
  for(const e of f.exprs)add({kind:"expression",pos:e.pos},e.type);
  for(const d of Array.isArray(f.unavailableTypes)?f.unavailableTypes:[]) {
    if(!d || typeof d.reason!=="string" || !/^[a-z][a-z0-9-]{0,79}$/.test(d.reason))continue;
    if(!["parameter","result","entry","expression"].includes(d.kind))continue;
    const entry={kind:d.kind,...(["entry","expression"].includes(d.kind)?{pos:d.pos}:{}),
      ...(["entry","parameter"].includes(d.kind)?{binding:d.binding}:{}),reason:d.reason};
    const k=key(entry);
    if(claims.get(k)===1)reasons.set(k,reasons.has(k)?null:entry);
  }
  return [...reasons.values()].filter(Boolean);
}

function fromSkjs(source, file, claims, producer) {
  if(!Array.isArray(claims))throw Error("expected SKJS file claims");
  const files=claims.filter(f=>f.file === file);
  if(files.length!==1)throw Error("expected exactly one matching claim file");
  return {version:1,source:{file,sha256:hash(source)},producer,
    functions:files[0].functions.map(f=>({name:f.name,namePos:f.namePos,
      ...(f.collection ? {collection:f.collection} : {}),
      unavailableTypes:unavailableTypes(f),
      signature:{params:f.params,retType:f.retType},
      entries:f.envs.map(e=>({pos:e.pos,bindings:e.vars.map(v=>({name:v.name,type:typeText(v.type),raw:v.type}))})),
      expressions:f.exprs.map(e=>({pos:e.pos,type:typeText(e.type),raw:e.type}))}))};
}

// Labels index the document's own type table; the first four rows are the
// primitives null, true, false and undefined.
function fromSourceClaims(source,file,input,producer) {
  const {typeText:labelText}=require("../report-viewer/obligation.js");
  if(input.version!==3||input.profile!=="stateful-source-v3"||input.file!==file||input.sourceSha256!==hash(source))
    throw Error("source-claim profile or source identity mismatch");
  const types=input.types;
  if(!Array.isArray(types)||types.length<4)throw Error("invalid source type table");
  const type=A=> {
    if(!Array.isArray(A)||A.some((i,k)=>!Number.isInteger(i)||i<0||i>=types.length||(k&&A[k-1]>=i)))throw Error("invalid source type labels");
    return labelText(types,A);
  };
  const point=b=> {
    if(!Object.hasOwn(b,"current"))throw Error("every source-claim point requires an explicit current field");
    const ordinary=type(b.type);
    if(b.current==null)return {type:ordinary,raw:b.type};
    const clause=b.type.length===1 ? types[b.type[0]]?.[0]?.refs : null;
    const invariant=clause&&!(clause.rest||[]).length ? clause.first : null;
    if(!invariant||!Array.isArray(b.current)||b.current.some(i=>!Number.isInteger(i)||i<0||i>=4))throw Error("invalid current-content assertion");
    return {type:`{ value: ${String(invariant)==="1,2"?"boolean":type(invariant)} = (${type(b.current)}) }`,
      raw:{type:b.type,current:b.current}};
  };
  const parameter=b=> {
    if(b.current!=null)throw Error("function parameters cannot carry current-content assertions");
    return {name:b.name,type:point(b).type};
  };
  const sf=parse(source,file),entries=new Map();
  const walk=n=>{if(ts.isStatement(n))entries.set(n.getStart(sf),n.end);n.forEachChild(walk);};walk(sf);
  return {version:1,source:{file,sha256:input.sourceSha256},producer,
    functions:input.functions.map(f=>({name:f.name,namePos:f.namePos,
      signature:{params:f.params.map(parameter),retType:type(f.result)},
      entries:f.entries.map(e=> {
        if(!entries.has(e.start))throw Error("source entry claim is not attached to a statement");
        return {pos:[e.start,entries.get(e.start)],bindings:e.bindings.map(b=>({name:b.name,...point(b)}))};
      }),expressions:f.expressions.map(e=>({pos:e.pos,...point(e)}))}))};
}

function attachConversion(source,report,sidecarBytes,conversion) {
  if(conversion.version!==1||conversion.kind!=="skjs-source-claim-conversion")throw Error("unsupported conversion manifest");
  if(conversion.source?.file!==report.source.file||conversion.source?.sha256!==hash(source))throw Error("conversion source identity mismatch");
  if(conversion.sidecarSha256!==hash(sidecarBytes))throw Error("conversion manifest does not match the exact sidecar; use a baseline for edited claims");
  if(!Array.isArray(conversion.omissions))throw Error("invalid conversion omissions");
  const original=fromSkjs(source,report.source.file,conversion.originalClaims,"skjs");
  render(source,original); // Validate original spans before using them for collection history.
  const result=clone(report);
  for(const f of result.functions) {
    const old=original.functions.find(g=>g.name===f.name&&g.namePos.join(":")===f.namePos.join(":"));
    if(!old)throw Error("conversion is missing the original function snapshot");
    if(old.collection) {
      f.collection=old.collection;f.collectionSource="original SKJS ";
      f.collectionSnapshot={entries:old.entries.map(e=>({pos:e.pos})),expressions:old.expressions.map(e=>({pos:e.pos}))};
    }
    f.conversionGaps=[];
    for(const omission of conversion.omissions) {
      if(omission.function!==f.name||JSON.stringify(omission.namePos)!==JSON.stringify(f.namePos))continue;
      const pos=omission.site?.pos;
      if(omission.site?.kind==="expression" && old.expressions.some(e=>JSON.stringify(e.pos)===JSON.stringify(pos)) &&
          !f.expressions.some(e=>JSON.stringify(e.pos)===JSON.stringify(pos))) {
        f.conversionGaps.push({pos,status:`expression claim omitted during conversion: ${omission.reason}`});
      }
    }
  }
  return result;
}

// The tree of the text the caller is holding, read as the file it names. A
// report is rendered over a source in memory — the original, or an annotated
// rendering of it — and its spans have to be spans of that text.
function parse(source, file) {
  return parseSource.openText(path.resolve(file), source);
}
/**
 * `identity` carries the report-level fingerprints and edit records into the
 * header comment and, where present, into the gap annotations.
 */
function render(source, report, results=null, identity: {claimChanges?:any[],[k:string]:any} = {}) {
  if(report.version!==1 || report.source?.sha256!==hash(source))throw Error("report source fingerprint mismatch");
  if(typeof report.producer!=="string" || !report.producer || !Array.isArray(report.functions))throw Error("invalid report header");
  if(results && results.length!==report.functions.length)throw Error("result count mismatch");
  const scanner=createScanner(false,undefined,source);
  for(let k=scanner.scan();k!==ts.SyntaxKind.EndOfFile;k=scanner.scan())
    if((k===ts.SyntaxKind.MultiLineCommentTrivia || k===ts.SyntaxKind.SingleLineCommentTrivia) &&
       /@verify-report\b/.test(scanner.getTokenText()))throw Error("source already contains report annotations; use the original source");
  const sf=parse(source,report.source.file), functions=new Map(), starts=new Set(), spans=new Set();
  function walk(n) {
    starts.add(n.getStart(sf));spans.add(`${n.getStart(sf)}:${n.end}`);
    if(ts.isFunctionDeclaration(n)&&n.name)functions.set(`${n.name.getStart(sf)}:${n.name.end}`,n);
    n.forEachChild(walk);
  }
  walk(sf);
  const insertions=new Map(), seen=new Set();
  function add(pos,data){insertions.set(pos,(insertions.get(pos)||"")+comment(data));}
  // Ids are positional and deterministic, so the manifest and the annotations
  // agree without either having to re-derive spans.
  const idOf=(kind,i,j=null)=>kind==="function" ? `f${i}` : kind==="gap" ? `g${i}` : `f${i}${kind==="entry"?"e":"x"}${j}`;
  const checkSpan = p => {
    if(!Array.isArray(p)||p.length!==2||!p.every(Number.isSafeInteger)||p[0]<0||p[0]>=p[1]||p[1]>source.length)
      throw Error("invalid source span");
  };
  for(const [index,f] of report.functions.entries()) {
    checkSpan(f.namePos);
    const key=f.namePos.join(":"), node=functions.get(key);
    if(!node || node.name.text!==f.name || seen.has(`fn:${key}`))throw Error("missing or duplicate function identity");
    seen.add(`fn:${key}`);
    if(!Array.isArray(f.entries)||!Array.isArray(f.expressions))throw Error("invalid function claims");
    add(node.getStart(sf),{kind:"function",id:idOf("function",index),name:f.name,producer:report.producer,
      collection:f.collection,collectionSource:f.collectionSource,
      ...(f.signature ? {signature:f.signature} : {}),
      ...(results ? {verification:results[index]} : {verification:{status:"not-run"}})});
    const at=(kind,q)=> {
      checkSpan(q.pos);
      if(q.pos[0]<node.getStart(sf)||q.pos[1]>node.end||!starts.has(q.pos[0]) ||
          (kind==="expression" && !spans.has(q.pos.join(":"))))throw Error(`cannot attach ${kind} claim at ${q.pos}`);
      const k=`${key}:${kind}:${q.pos[0]}:${kind==="expression" ? q.pos[1] : ""}`;
      if(seen.has(k))throw Error("duplicate claim attachment");seen.add(k);
    };
    for(const [j,q] of f.entries.entries()) {
      at("entry",q);
      if(!Array.isArray(q.bindings)||new Set(q.bindings.map(b=>b.name)).size!==q.bindings.length ||
         q.bindings.some(b=>typeof b.name!=="string"||typeof b.type!=="string"))throw Error("invalid entry bindings");
      add(q.pos[0],{kind:"entry",id:idOf("entry",index,j),originalSpan:q.pos,producer:report.producer,
        quality:f.collection?.quality,bindings:q.bindings.map(({name,type})=>({name,type})),
        unsupported:q.bindings.filter(b=>b.raw&&b.raw.unsupported).map(b=>b.name),status:"producer-claim"});
    }
    for(const [j,q] of f.expressions.entries()) {
      at("expression",q);
      if(typeof q.type!=="string")throw Error("invalid expression claim");
      add(q.pos[0],{kind:"expression",id:idOf("expression",index,j),originalSpan:q.pos,producer:report.producer,
        quality:f.collection?.quality,type:q.type,status:"producer-claim"});
    }
  }
  const gaps=coverage(source,report);
  for(const gap of gaps)add(gap.pos[0],{kind:"gap",id:gap.id,originalSpan:gap.pos,detail:gap.status});
  for(const [i,change] of (identity.claimChanges||[]).entries())add(change.span[0],
    {kind:"gap",id:idOf("gap",gaps.length+i),originalSpan:change.span,
     detail:`claim edit: ${change.status} ${change.kind}; see manifest for before/after`});
  // No new line terminators: preserve return/throw/async automatic-semicolon behavior.
  // Hashbang and BOM, when present, must remain at the beginning of the file.
  const headerAt=source.startsWith("#!") ? (source.indexOf("\n")<0 ? source.length : source.indexOf("\n")+1)
    : source.charCodeAt(0)===0xfeff ? 1 : 0;
  const header=comment({kind:"report",version:1,source:report.source,producer:report.producer,
    notice:"Display only. Results cover modeled function obligations, not every exported claim. Re-extract and verify after edits.",...identity});
  insertions.set(headerAt,header+(insertions.get(headerAt)||""));
  let text=source;
  for(const [pos,data] of [...insertions].sort((a,b)=>b[0]-a[0]))text=text.slice(0,pos)+data+text.slice(pos);
  // Adding comments must not change the program. Two independent witnesses of
  // that: the token stream with trivia skipped, which is what the parser
  // actually consumes, and the tree of node kinds it produced.
  const annotated=parse(text,report.source.file);
  if(JSON.stringify(tokens(source))!==JSON.stringify(tokens(text)) ||
     JSON.stringify(shape(sf))!==JSON.stringify(shape(annotated)))
    throw Error("annotation changed the source AST");
  return text;
}

// Every token, comments and whitespace skipped, as kind and spelling.
function tokens(text) {
  const scanner=createScanner(true,undefined,text), out=[];
  for(let k=scanner.scan();k!==ts.SyntaxKind.EndOfFile;k=scanner.scan())out.push([k,scanner.getTokenText()]);
  return out;
}
const shape=n=>{const kids=[];n.forEachChild(c=>{kids.push(shape(c));});return [n.kind,kids];};

// Absence is meaningful only when the producer explicitly records collection progress.
function coverage(source,report) {
  const sf=parse(source,report.source.file), gaps=[];
  for(const node of sf.statements) {
    if(!ts.isFunctionDeclaration(node)||!node.name||!node.body)continue;
    const f=report.functions.find(f=>f.namePos[0]===node.name.getStart(sf)&&f.namePos[1]===node.name.end);
    if(!f){gaps.push({pos:[node.getStart(sf),node.end],status:"claims unavailable; verification not established"});continue;}
    const snapshot=f.collectionSnapshot||f;
    for(const gap of f.conversionGaps||[])gaps.push(gap);
    if(!f.collection)continue;
    for(const pos of f.collection.visitedExpressions||[]) {
      if(!snapshot.expressions.some(e=>e.pos[0]===pos[0]&&e.pos[1]===pos[1])) {
        if(!Array.isArray(pos)||pos.length!==2||!pos.every(Number.isSafeInteger)||pos[0]<node.getStart(sf)||pos[1]>node.end||pos[0]>=pos[1])throw Error("invalid expression visit span");
        const matches=n=>(n.getStart(sf)===pos[0]&&n.end===pos[1])||n.forEachChild(matches);
        if(!matches(node))throw Error("cannot attach expression visit");
        gaps.push({pos,status:"expression entered without a type result"});
      }
    }
    if(f.collection.completion==="aborted") {
      const walk=n=> {
        if(ts.isFunctionDeclaration(n))return;
        if((ts.isVariableStatement(n)||ts.isReturnStatement(n)||ts.isIfStatement(n)||ts.isWhileStatement(n)||ts.isExpressionStatement(n)) &&
           !snapshot.entries.some(e=>e.pos[0]===n.getStart(sf)))gaps.push({pos:[n.getStart(sf),n.end],status:"statement not visited"});
        n.forEachChild(walk);
      };
      walk(node.body);
    }
  }
  // One id per gap, assigned in one place so every gap kind is joinable to the manifest.
  return gaps.map((g,i)=>({id:`g${i}`,...g}));
}

// Compare candidates, never saved proof results. Object property order is immaterial.
const canonical = x => JSON.stringify(normalize(x));
function normalize(x) {
  if(Array.isArray(x))return x.map(normalize);
  if(x && typeof x==="object")return Object.fromEntries(Object.keys(x).sort().map(k=>[k,normalize(x[k])]));
  return x;
}
function compareClaims(source,baseline,current) {
  if(baseline.source?.file!==current.source?.file)throw Error("baseline source identity mismatch");
  render(source,baseline);render(source,current); // Includes exact source digest and attachment validation.
  const sites=report=> {
    const out=new Map();
    for(const f of report.functions) {
      const put=(kind,span,value)=>out.set(`${f.namePos.join(":")}:${kind}:${kind==="entry"?span[0]:span.join(":")}`,
        {kind,function:f.name,span,value});
      put("function",f.namePos,f.signature||null);
      for(const e of f.entries)put("entry",e.pos,
        e.bindings.map(b=>({name:b.name,type:b.raw??b.type})).sort((a,b)=>a.name<b.name?-1:a.name>b.name?1:0));
      for(const e of f.expressions)put("expression",e.pos,e.raw??e.type);
    }
    return out;
  };
  const before=sites(baseline),after=sites(current),changes=[];
  for(const key of new Set([...before.keys(),...after.keys()])) {
    const a=before.get(key),b=after.get(key);
    if(a&&b&&canonical(a.value)===canonical(b.value))continue;
    const {value,...site}=b||a;
    changes.push({...site,status:!a?"added":!b?"removed":"changed",
      ...(a?{before:a.value}:{}),...(b?{after:b.value}:{})});
  }
  changes.sort((a,b)=>a.span[0]-b.span[0]||a.kind.localeCompare(b.kind));
  return {baselineProducer:baseline.producer,changes};
}

function run(executable,args) {
  const r=spawnSync(executable,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});
  if(r.error || r.signal)throw Error(`tool execution failed: ${r.error?.message || r.signal}`);
  return r;
}
const {readDiagnostic}=require("./obligation-diagnostic.mts");
function verifySkjs(sourcePath, source, claims, file, report, verifier, depth, normalized=false) {
  const parser=path.join(__dirname,"parse-source.mts"), temp=fs.mkdtempSync(path.join(os.tmpdir(),"annotated-source-"));
  try {
    // Called rather than spawned: a node start costs more than the parse, and
    // this runs once per source. The parser's own file is still hashed into the
    // identity, so what ran is recorded either way.
    const identity={verifierSha256:hash(fs.readFileSync(verifier)),parserSha256:hash(fs.readFileSync(parser))};
    let ast;
    try {
      ast=parseSource.parseFile(sourcePath);
    } catch(error) {
      const detail=String((error as Error)?.message||error);
      if(!detail.startsWith("gate:"))throw Error(`source parser failed: ${detail}`);
      return {identity,results:report.functions.map(()=>({status:"unsupported",detail:detail.trim()}))};
    }
    ast.file=file;
    // Whole file first. The per-function pass below exists to attribute a
    // failure to the function it belongs to; when nothing fails there is
    // nothing to attribute, and one produce/check covers every function in the
    // file. That is the same evidence, from the same two commands, at two
    // processes instead of two per function.
    const whole=(()=>{
      const c=normalized ? clone(claims) : clone(claims).filter(g=>g.file===file);
      if(!normalized) {
        const selected=c[0];
        if(!selected)return null;
        for(const g of selected.functions)delete g.unavailableTypes;
      }
      const ap=path.join(temp,"whole.ast.json"), cp=path.join(temp,"whole.claims.json"), ep=path.join(temp,"whole.evidence.json");
      fs.writeFileSync(ap,JSON.stringify(ast));fs.writeFileSync(cp,JSON.stringify(c));
      const produced=run(verifier,[normalized?"--produce-source-claims":"--produce-stateful-source",ap,cp,file,ep,String(depth)]);
      if(produced.status!==0)return null;
      const checked=run(verifier,[normalized?"--check-source-claims":"--check-stateful-source",ap,cp,file,ep]);
      if(checked.status!==0)return null;
      const certificateSha256=hash(fs.readFileSync(ep));
      return report.functions.map(()=>({status:"verified",scope:"modeled function and required claims",certificateSha256}));
    })();
    if(whole) {
      if(fs.readFileSync(sourcePath,"utf8")!==source)throw Error("source changed during verification");
      return {identity,results:whole};
    }
    const results=report.functions.map(f=> {
      const a=clone(ast);a.functions=a.functions.filter(g=>g.name===f.name && JSON.stringify(g.namePos)===JSON.stringify(f.namePos));
      if(a.functions.length!==1)throw Error("function identity mismatch during verification");
      const c=normalized ? clone(claims) : clone(claims).filter(g=>g.file===file);
      const selected=normalized ? c : c[0];
      selected.functions=selected.functions.filter(g=>g.name===f.name && JSON.stringify(g.namePos)===JSON.stringify(f.namePos));
      const refusals=normalized ? [] : unavailableTypes(selected.functions[0]);
      // Metadata is for reporting only, excluded from verifier input and its digest.
      if(!normalized)for(const g of selected.functions)delete g.unavailableTypes;
      const ap=path.join(temp,"ast.json"), cp=path.join(temp,"claims.json"), ep=path.join(temp,"evidence.json");
      fs.writeFileSync(ap,JSON.stringify(a));fs.writeFileSync(cp,JSON.stringify(c));
      const produced=run(verifier,[normalized?"--produce-source-claims":"--produce-stateful-source",ap,cp,file,ep,String(depth)]);
      if(produced.status!==0) {
        const rawDetail=(produced.stderr||produced.stdout).trim();
        const diagnostic=readDiagnostic(rawDetail);
        const detail=diagnostic ? rawDetail.split("\nobligation-diagnostic: ")[0] : rawDetail;
        const located=/^(?:reject: )?(source expression obligation|closure expression claim|source incoming edge obligation|unsupported source expression) at \[(\d+),(\d+)\):/.exec(detail);
        const environment=/^(?:reject: )?source environment obligation at (\d+): (.*)$/.exec(detail);
        // A claim the extractor needed and did not find is a different finding
        // from a claim whose proof search failed: the report already marks that
        // place as a gap, and naming it lets a reader see the two together.
        const absentExpr=/^(?:reject: )?no claimed type for the expression at \[(\d+),(\d+)\)$/.exec(detail);
        const absentEnv=environment && /^missing statement environment at \d+$/.test(environment[2]);
        const absentBinding=environment && /^missing claimed binding '([^']*)' at \d+$/.exec(environment[2]);
        // A fragment limitation reported without a span still says checking never
        // started on this function; it is not a failed proof search.
        const unavailableBinding=environment && /^unavailable claimed binding '([^']*)' at \d+$/.exec(environment[2]);
        const unavailableType=unavailableBinding || /type claim unavailable from producer$/.test(detail);
        const nonInvariant=/cell read and write types do not describe the same invariant$/.test(detail);
        // The producer's parameter claim contradicts the annotation the caller
        // is held to: a finding about the claim, before any obligation is tried.
        const parameterClaim=/claimed parameter type differs from the source annotation for '([^']*)'$/.exec(detail);
        const outsideSlice=/outside the [^:]*slice\.?$/.test(detail);
        const location=parameterClaim ? {kind:"parameter-claim",binding:parameterClaim[1]} : unavailableType ? {kind:"unavailable-type-claim",
          ...(unavailableBinding ? {start:Number(environment[1]),binding:unavailableBinding[1]} :
            located ? {pos:[Number(located[2]),Number(located[3])]} : {})} : nonInvariant ? {kind:"source-limitation",reason:"non-invariant-cell-contract",
          ...(environment ? {start:Number(environment[1])} : located ? {pos:[Number(located[2]),Number(located[3])]} : {})} : located ? {kind:located[1]==="unsupported source expression" ? "source-limitation" : located[1]==="source incoming edge obligation" ? "edge-obligation" : "expression-obligation",pos:[Number(located[2]),Number(located[3])]} :
          absentExpr ? {kind:"missing-expression-claim",pos:[Number(absentExpr[1]),Number(absentExpr[2])]} :
          absentEnv ? {kind:"missing-environment-claim",start:Number(environment[1])} :
          absentBinding ? {kind:"missing-environment-claim",start:Number(environment[1]),binding:absentBinding[1]} :
          environment ? {kind:"environment-obligation",start:Number(environment[1])} :
          outsideSlice ? {kind:"source-limitation"} : null;

        // One shape for every branch above: a place (a span or an entry start),
        // the binding it concerns where there is one, and the producer's own
        // reason where the refusals below match it.
        const where = location as {kind:string,pos?:number[],start?:number,binding?:string,reason?:string}|null;
        if(unavailableType && where) {
          const matches=refusals.filter(d=>unavailableBinding ?
            d.kind==="entry"&&d.pos[0]===where.start&&d.binding===where.binding :
            located ? d.kind==="expression"&&JSON.stringify(d.pos)===JSON.stringify(where.pos) : false);
          if(matches.length===1)where.reason=matches[0].reason;
        }
        // Bind node-local IDs to this exact function, source, and selected claims.
        const obligation=diagnostic ? {...diagnostic,input:{file,functionName:f.name,
          namePos:f.namePos,sourceSha256:hash(source),claimsSha256:hash(JSON.stringify(c))}} : null;
        return {status:"not-established",detail,...((unavailableType || nonInvariant) ? {stage:"source-extraction"} : {}),...(location ? {location} : {}),
          ...(obligation ? {obligation} : {})};
      }
      const checked=run(verifier,[normalized?"--check-source-claims":"--check-stateful-source",ap,cp,file,ep]);
      if(checked.status!==0)return {status:"not-established",detail:(checked.stderr||checked.stdout).trim()};
      return {status:"verified",scope:"modeled function and required claims",certificateSha256:hash(fs.readFileSync(ep))};
    });
    if(fs.readFileSync(sourcePath,"utf8")!==source)throw Error("source changed during verification");
    return {identity,results};
  } finally {fs.rmSync(temp,{recursive:true,force:true});}
}

function checkFresh(output) {
  const m=JSON.parse(fs.readFileSync(output+".json","utf8"));
  const checks=[[output,m.annotatedSha256],[m.sourcePath,m.source.sha256],[m.claimsPath,m.claimsSha256]];
  if(m.conversionPath)checks.push([m.conversionPath,m.conversionSha256]);
  if(m.baselinePath)checks.push([m.baselinePath,m.baselineSha256]);
  if(m.diagnosticsPath)checks.push([m.diagnosticsPath,m.diagnosticsSha256]);
  if(m.verifierPath)checks.push([m.verifierPath,m.verifierSha256]);
  if(m.parserSha256)checks.push([path.join(__dirname,"parse-source.mts"),m.parserSha256]);
  for(const [file,digest] of checks)if(hash(fs.readFileSync(file))!==digest)throw Error(`stale report: ${file}`);
  console.log("Snapshot fingerprints match. This is not proof verification.");
}

// These are possible attachment sites, not obligations inferred by this reader.
// The existing source adapter and verifier decide which claims are required.
// An environment claim must bind every name in scope, so a reader authoring one
// needs to know what those names are. Their source annotations come with them:
// the surface reader cannot write a function or record type without a template,
// since inventing the fields the surface does not name is what it refuses to do.
// A type outside the source fragment translates to null, which the reader shows
// as undecoded rather than guessing at.
const namedBinding=(name,typeNode)=>{
  let type=null;
  try{type=typeNode?parseSource.typeOf(typeNode):null;}catch(e){type=null;}
  return {name,type};
};
const identifiers=nodes=>(nodes||[]).filter(p=>ts.isIdentifier(p.name)).map(p=>[p.name.text,p.type]);
const declaredBy=n=>ts.isVariableStatement(n)?identifiers(n.declarationList.declarations):[];

// TypeScript's own "is this node in expression position" test is not part of
// the public surface, and kind alone is not it: the name a declaration binds
// is an Identifier like any other. The name a node *declares* is always its
// `name` child — with one exception, a property access, whose `.value` is not
// a declared name but part of the expression, and carries a claim like any
// other site.
const isDeclaredName = n => {
  const p=n.parent;
  return !!p && p.name===n && !ts.isPropertyAccessExpression(p);
};
const isExpressionNode = n => ts.isExpression(n) && !isDeclaredName(n);

function missingClaimSites(node, f) {
  const sites=[];
  const walk=(n,scope)=> {
    if(ts.isFunctionDeclaration(n)||ts.isTypeNode(n))return;
    const pos=[n.getStart(),n.end];
    if(ts.isStatement(n) && !ts.isBlock(n) && !f.entries.some(e=>e.pos[0]===pos[0]))
      sites.push({kind:"environment",pos,syntax:ts.isVariableStatement(n)?"VariableStatement":ts.SyntaxKind[n.kind],
        bindings:scope.map(([name,typeNode])=>namedBinding(name,typeNode))});
    if(isExpressionNode(n) && !f.expressions.some(e=>e.pos[0]===pos[0]&&e.pos[1]===pos[1]))
      sites.push({kind:"expression",pos,syntax:ts.SyntaxKind[n.kind]});
    // A block is walked in order so that each statement sees only what precedes
    // it; a lambda adds its own parameter for its body.
    if(ts.isBlock(n)) {
      let inner=scope;
      for(const st of n.statements) { walk(st,inner); inner=inner.concat(declaredBy(st)); }
      return;
    }
    if(ts.isArrowFunction(n)||ts.isFunctionExpression(n)) {
      const inner=scope.concat(identifiers(n.parameters));
      n.forEachChild(c=>walk(c,inner));
      return;
    }
    n.forEachChild(c=>walk(c,scope));
  };
  if(node.body) walk(node.body,identifiers(node.parameters));
  return sites.sort((a,b)=>a.pos[0]-b.pos[0]||a.pos[1]-b.pos[1]);
}

function main(args) {
  if(args[0]==="--check-fresh" && args.length===2)return checkFresh(args[1]);
  const sourcePath=args.shift();
  // Every switch in `allowed` below lands here, so the record says so once
  // rather than growing a property at a time.
  const options = {format:"skjs",depth:10} as {
    format:string, depth:string|number, claims?:string, out?:string, verify?:string,
    producer?:string, "file-key"?:string, diagnostics?:string, baseline?:string,
    conversion?:string, stdout?:string,
  };
  if(!sourcePath)throw Error("usage: annotate-source.mts source.ts --claims claims.json [--out annotated.ts] [--verify verifier] [--format report --producer name]");
  const allowed=new Set(["claims","out","verify","format","producer","file-key","depth","diagnostics","baseline","conversion","stdout"]);
  while(args.length) {
    const key=args.shift()?.replace(/^--/,"");
    if(!allowed.has(key)||!args.length)throw Error(`invalid option ${key}`);
    options[key]=args.shift();
  }
  options.producer ??= options.conversion ? "skjs (converted)" : options.format==="skjs" ? "skjs" : "unspecified";
  if(!options.claims || !["skjs","report","source-claims"].includes(options.format))throw Error("expected --claims and a supported format");
  if(!/^\d+$/.test(String(options.depth))||!Number.isSafeInteger(Number(options.depth)))throw Error("invalid proof depth");
  if(options.format==="report"&&options.verify)throw Error("verification of generic report inputs needs a producer adapter; stored statuses are never trusted");
  const output=options.out || sourcePath.replace(/\.ts$/,"")+".annotated.ts", manifest=output+".json";
  if([sourcePath,options.claims,options.verify].filter(Boolean).some(p=>path.resolve(p)===path.resolve(output)))throw Error("output must differ from inputs");
  // Nothing is written in stdout mode, so an existing report there is not a conflict.
  if(options.stdout!=="json" && (fs.existsSync(output)||fs.existsSync(manifest)))throw Error("output already exists; choose a new --out path");
  const source=fs.readFileSync(sourcePath,"utf8"), bytes=fs.readFileSync(options.claims,"utf8"), input=JSON.parse(bytes);
  const file=options["file-key"] || sourcePath;
  let report=options.format==="skjs" ? fromSkjs(source,file,input,options.producer) : options.format==="source-claims" ? fromSourceClaims(source,file,input,options.producer) : input;
  let conversion=null,conversionBytes=null;
  if(options.conversion) {
    if(options.format!=="source-claims")throw Error("--conversion requires --format source-claims");
    conversionBytes=fs.readFileSync(options.conversion,"utf8");conversion=JSON.parse(conversionBytes);
    report=attachConversion(source,report,bytes,conversion);
  }
  // Validate attachment before running any expensive proof generation.
  render(source,report);
  let results=null, comparison=null;
  let identity: {claimsSha256:string, [k:string]:any} = {claimsSha256:hash(bytes)};
  if(conversion)identity.conversionSha256=hash(conversionBytes);
  if(options.baseline) {
    const baselineBytes=fs.readFileSync(options.baseline,"utf8");
    comparison=compareClaims(source,JSON.parse(baselineBytes),report);
    identity.baselineSha256=hash(baselineBytes);
  }
  if(options.verify) {
    const verified=verifySkjs(sourcePath,source,input,file,report,path.resolve(options.verify),Number(options.depth),options.format==="source-claims");
    results=verified.results;identity={...identity,...verified.identity};
  }
  const diagnostics=options.diagnostics ? fs.readFileSync(options.diagnostics,"utf8") : null;
  if(diagnostics!==null)identity.diagnosticsSha256=hash(diagnostics);
  const annotated=render(source,report,results,{...identity,...(comparison?{claimChanges:comparison.changes}:{}),...(conversion?{conversionOmissions:conversion.omissions}:{})});
  const functionNodes=parse(source,report.source.file).statements.filter(ts.isFunctionDeclaration);
  const data={version:1,sourcePath:path.resolve(sourcePath),claimsPath:path.resolve(options.claims),
    ...(options.verify ? {verifierPath:path.resolve(options.verify)} : {}),
    ...identity,source:report.source,annotatedSha256:hash(annotated),producer:report.producer,
    ...(options.diagnostics ? {diagnosticsPath:path.resolve(options.diagnostics),diagnostics} : {}),
    ...(conversion?{conversionPath:path.resolve(options.conversion),conversion}:{}),
    ...(comparison?{baselinePath:path.resolve(options.baseline),comparison}:{}),
    missingFunctions:functionNodes.filter(n=>n.name && n.body && !report.functions.some(f=>f.namePos[0]===n.name.getStart())).map(n=>({
      name:n.name.text,namePos:[n.name.getStart(),n.name.end],pos:[n.getStart(),n.end],
      parameters:n.parameters.map(p=>p.name.getText()),missingSites:missingClaimSites(n,{entries:[],expressions:[]})})),
    gaps:coverage(source,report),
    functions:report.functions.map((f,i)=>({id:`f${i}`,...f,
      ...((node)=>({pos:[node.getStart(),node.end],missingSites:missingClaimSites(node,f)}))(
        functionNodes.find(n=>n.name?.getStart()===f.namePos[0])),
      entries:f.entries.map((e,j)=>({id:`f${i}e${j}`,...e})),
      expressions:f.expressions.map((e,j)=>({id:`f${i}x${j}`,...e}))})),
    results:results ? results.map((r,i)=>({function:`f${i}`,...r})) : results};
  if(options.stdout === "json"){
    // For callers that want the report without leaving files behind.
    process.stdout.write(JSON.stringify({annotated,manifest:data})+"\n");
    return;
  }
  fs.writeFileSync(output,annotated,{flag:"wx"});
  try {fs.writeFileSync(manifest,JSON.stringify(data,null,2)+"\n",{flag:"wx"});}
  catch(e){fs.unlinkSync(output);throw e;}
  console.log(`Annotated source: ${output}\nReport manifest: ${manifest}`);
}
export {hash,typeText,fromSkjs,fromSourceClaims,attachConversion,render,coverage,compareClaims,verifySkjs,main};
if(process.argv[1] && import.meta.filename===path.resolve(process.argv[1]))
  try {main(process.argv.slice(2));}catch(e){console.error((e as Error).message);process.exitCode=1;}
