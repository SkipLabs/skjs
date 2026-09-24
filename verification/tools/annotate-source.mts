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
import surface from "./claim-text.mts";
import obligationReader, { presentObligation } from "../tools/diagnostic-view.mts";
import { readDiagnostic } from "./diagnostic.mts";
// The source annotation encoding has exactly one implementation; a second
// would be a second opinion about what a source type means.
import * as fragmentParse from "./fragment-parse.mts";
import { claimOfTerm } from "./term-claim.mts";
import { tsconfigOf } from "./declaration-graph.mts";
import type {
  Labels,
  NamedPoint,
  Point,
  SourceClaims,
} from "./source-claims.mts";
import type { Span } from "./span.mts";
import type { Failure, Result } from "../report-viewer/types.ts";
import type { SkjsFile, SkjsFunction } from "./skjs-claims.mts";
import type { ConversionManifest } from "./export-source-claims.mts";
import { messageOf } from "./thrown.mts";
import { rigidOf, rigidScopes, scopeOf } from "./rigid.mts";
import type { RigidParameter, RigidScopes } from "./rigid.mts";
type FunctionResult = Result extends infer R
  ? R extends Result
    ? Omit<R, "function">
    : never
  : never;
const __dirname = path.dirname(new URL(import.meta.url).pathname);
// The display helpers beside this file are plain JavaScript modules.
const require = createRequire(import.meta.url);
/* --------------------------------------------------------- reading a value -- */
// Claims, manifests and reports arrive as JSON, so what a value is has to be
// tested before it is read. `Array.isArray` alone widens `unknown` to `any[]`,
// which is how the elements stop being checked; `isList` keeps them unknown.
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object";
const isList = (v: unknown): v is unknown[] => Array.isArray(v);
/* ------------------------------------------------------------- the shapes -- */
// A report is built in two steps: a converter turns a producer's claims into
// the fields below, and `main` attaches the positional ids and declaration
// spans the reader indexes by (report-viewer/types.ts describes what the
// reader then sees). These are the intermediate, and the producer inputs they
// are built from. A `--format report` document another producer wrote arrives
// in the same shape and is rendered by the same code, so these describe both.
// Spans are number lists here because that is what a document carries:
// `checkSpan` is what makes one a span.

/** One claim, as the report carries it: surface text beside the encoding. */
interface DraftClaim {
  pos: number[];
  type: string;
  raw?: unknown;
  /** The rigid parameters this claim names, with their declared bounds. */
  rigid?: RigidParameter[];
}
interface DraftBinding {
  name: string;
  type: string;
  raw?: unknown;
  rigid?: RigidParameter[];
}
interface DraftEntry {
  pos: number[];
  bindings: DraftBinding[];
}
/** A type the producer could not state, addressed to the exact claim it covers. */
interface Unavailable {
  kind: "parameter" | "result" | "entry" | "expression";
  pos?: Span;
  binding?: string;
  reason: string;
}
/**
 * Collection metadata as a report document carries it, which is not yet
 * checked: `Collection` in report-viewer/types.ts names the same fields once a
 * report has been read back, and `SkjsCollection` names them as the producer's
 * own export carries them.
 */
interface DraftCollection {
  completion: string;
  quality: string;
  mode: string;
  /** Original spans expression checking entered (ANNOTATED-SOURCE.md). */
  visitedExpressions?: number[][];
}
/** A function as `render` finds it in a document: everything a producer may
 * leave unstated is optional, and nothing is trusted until it is checked. */
interface InputFunction {
  name: string;
  namePos: number[];
  /** The rigid parameters the source declares for it, with their bounds. */
  typeParams?: RigidParameter[];
  signature?: {
    params: { name: string; type: unknown }[];
    retType: unknown;
    /** The parameters the claimed result names. */
    resultRigid?: RigidParameter[];
  };
  entries: DraftEntry[];
  expressions: DraftClaim[];
  unavailableTypes?: Unavailable[];
  /** How complete the producer's own collection was; absent if it said nothing. */
  collection?: DraftCollection;
  /** Attached by `attachConversion`, which carries the original's history over. */
  collectionSource?: string;
  collectionSnapshot?: {
    entries: { pos: number[] }[];
    expressions: { pos: number[] }[];
  };
  conversionGaps?: { pos: number[]; status: string }[];
}
interface ReportInput {
  source: { file: string; sha256: string };
  producer: string;
  functions: InputFunction[];
  /** Only ever read to be ignored: a stored status is never evidence. */
  results?: unknown;
}
/** What the converters below build, which states a signature for every
 * function and carries the producer's own collection metadata. */
interface DraftFunction extends InputFunction {
  signature: {
    params: { name: string; type: unknown }[];
    retType: unknown;
    resultRigid?: RigidParameter[];
  };
}
interface DraftReport extends ReportInput {
  functions: DraftFunction[];
}



/** One site where a candidate's claim differs from its baseline. */
interface ClaimChange {
  kind: string;
  function: string;
  span: number[];
  status: "added" | "removed" | "changed";
  before?: unknown;
  after?: unknown;
}

/**
 * The report-level fingerprints and edit records `render` carries into the
 * header comment and, where present, into the gap annotations.
 */
interface ReportIdentity {
  claimsSha256?: string;
  conversionSha256?: string;
  baselineSha256?: string;
  verifierSha256?: string;
  diagnosticsSha256?: string;
  claimChanges?: ClaimChange[];
  conversionOmissions?: ConversionManifest["omissions"];
}

/* -------------------------------------------------------- the annotations -- */
/** What any annotation may carry beside the fields its own kind requires. */
interface AnnotationBase {
  /** Joins the comment to its manifest record. */
  id?: string;
  /** The producer's own span for a claim, as it was before annotation. */
  originalSpan?: number[];
  /** `recovery` where the producer's own collection says so. */
  quality?: string;
  /** Names the producer could not decode at this site. */
  unsupported?: string[];
}
interface ReportAnnotation extends AnnotationBase, ReportIdentity {
  kind: "report";
  source: { file: string; sha256: string };
  producer: string;
  notice: string;
}
interface FunctionAnnotation extends AnnotationBase {
  kind: "function";
  name: string;
  producer: string;
  signature?: InputFunction["signature"];
  collection?: DraftCollection;
  collectionSource?: string;
  verification: { status: string; detail?: string };
}
interface EntryAnnotation extends AnnotationBase {
  kind: "entry";
  producer: string;
  bindings: { name: string; type: string }[];
  status: string;
}
interface ExpressionAnnotation extends AnnotationBase {
  kind: "expression";
  producer: string;
  type: string;
  status: string;
}
interface GapAnnotation extends AnnotationBase {
  kind: "gap";
  detail: string;
}
type Annotation =
  | ReportAnnotation
  | FunctionAnnotation
  | EntryAnnotation
  | ExpressionAnnotation
  | GapAnnotation;

const hash = (data: crypto.BinaryLike) =>
  crypto.createHash("sha256").update(data).digest("hex");
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
// Escapes what could end or break the comment; a quote cannot, and a string
// literal reads better unescaped. A backslash stays doubled, so the text is
// still decodable: "\\" is one backslash, '"' is one quote.
const safeText = (x: unknown) => JSON.stringify(String(x)).slice(1,-1).replace(/\\"/g,'"').replace(/\*\//g,"*\\/").replace(/[\u2028\u2029]/g,c=>c==="\u2028"?"\\u2028":"\\u2029");
// Every annotation carries its kind, a stable id joining it to the manifest, and,
// for a gap, the reason as a slug. The prose stays: these comments are read by
// people as well as by tools, and a reworded sentence must not break a reader.
const reasons: Record<string, string> = {
  "statement not visited":"statement-not-visited",
  "expression entered without a type result":"expression-without-type",
  "claims unavailable; verification not established":"claims-unavailable"};
const reasonSlug = (detail: string) => reasons[detail] ||
  (/^claim edit:/.test(detail) ? "claim-edit"
   : detail.toLowerCase().replace(/[^a-z0-9]+/g,"-").replace(/^-|-$/g,"").split("-").slice(0,4).join("-"));
function fields(x: Annotation) {
  const parts=["kind="+x.kind];
  if(x.kind === "gap")parts.push("reason="+reasonSlug(x.detail));
  if(x.id)parts.push("id="+x.id);
  if(x.unsupported && x.unsupported.length)parts.push("unsupported="+x.unsupported.join("+"));
  return parts.join("; ")+"; ";
}
function comment(x: Annotation) {
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

// An atom is a record of its own fields. What arrives may not be one, and the
// tests below are what say so; a nullish element reaches `Object.keys` exactly
// as it did before there was a type here.
const isAtomList = (v: unknown): v is Record<string, unknown>[] => Array.isArray(v);

function typeText(t: unknown) {
  if(typeof t==="string")return t;
  // A binding the producer could not decode has no claimed type. Name the
  // absence instead of printing an encoding that reads like a type; the exact
  // payload stays in the manifest, joined by the annotation id.
  if(isRecord(t) && t.unsupported === true && Object.keys(t).length === 1)return "(unavailable)";
  // Surface syntax where the printer can name the type; the exact encoding
  // otherwise, so a shape it does not know is never quietly hidden.
  const printed=surface.printType(t);
  if(printed.printable)return printed.text;
  if(isRecord(t) && t.top === false && Object.keys(t).sort().join() === "atoms,top" && isAtomList(t.atoms)) {
    const names=t.atoms.map(a=> {
      if(Object.keys(a).join() === "a" && typeof a.a === "string" && ["null","boolean","string","number","undefined"].includes(a.a))return a.a;
      if(Object.keys(a).sort().join() !== "a,v")return null;
      // Literal types are displayed as the literal they are. Nothing is dropped:
      // the exact payload stays in the manifest, joined by the annotation id.
      if(a.a === "booleanlit" && typeof a.v === "string" && ["true","false"].includes(a.v))return a.v;
      if(a.a === "stringlit" && typeof a.v === "string")return JSON.stringify(a.v);
      if((a.a === "numberlit" || a.a === "numlit") && Number.isFinite(Number(a.v)))return String(a.v);
      return null;
    });
    if(names.every((x: unknown)=>x!==null))return names.length ? names.join(" | ") : "never";
  }
  return JSON.stringify(t);
}

// Advisory exporter metadata is bound to an exact claim address. Ignore stale,
// malformed and ambiguous entries; none can turn an unavailable type into evidence.
const isRefusalKind=(k: unknown): k is Unavailable["kind"]=>
  k==="parameter"||k==="result"||k==="entry"||k==="expression";
function unavailableTypes(f: SkjsFunction): Unavailable[] {
  const missing=(t: unknown)=>isRecord(t) && t.unsupported===true && Object.keys(t).length===1;
  const key=(kind: unknown, pos: unknown, binding: unknown)=>JSON.stringify([kind,pos,binding]);
  // Each address is kept with the claim that owns it, so a reason is attached
  // to the span this file read rather than to the one the metadata repeats.
  const claims=new Map<string, {count: number, at: Partial<Unavailable>}>(),
    reasons=new Map<string, Unavailable|null>();
  const add=(d: Partial<Unavailable>, t: unknown)=>{
    if(!missing(t))return;
    const k=key(d.kind,d.pos,d.binding);
    claims.set(k,{count:(claims.get(k)?.count||0)+1,at:d});
  };
  for(const p of f.params)add({kind:"parameter",binding:p.name},p.type);
  add({kind:"result"},f.retType);
  for(const e of f.envs)for(const v of e.vars)add({kind:"entry",pos:e.pos,binding:v.name},v.type);
  for(const e of f.exprs)add({kind:"expression",pos:e.pos},e.type);
  for(const d of isList(f.unavailableTypes)?f.unavailableTypes:[]) {
    if(!isRecord(d) || typeof d.reason!=="string" || !/^[a-z][a-z0-9-]{0,79}$/.test(d.reason))continue;
    if(!isRefusalKind(d.kind))continue;
    const k=key(d.kind,["entry","expression"].includes(d.kind)?d.pos:undefined,
      ["entry","parameter"].includes(d.kind)?d.binding:undefined);
    const claim=claims.get(k);
    if(claim?.count===1)reasons.set(k,reasons.has(k)?null:{...claim.at,kind:d.kind,reason:d.reason});
  }
  return [...reasons.values()].filter(d=>d!==null);
}

function fromSkjs(
  source: string,
  file: string,
  claims: SkjsFile[],
  producer: string,
): DraftReport {
  if(!Array.isArray(claims))throw Error("expected SKJS file claims");
  const files=claims.filter(f=>f.file === file);
  if(files.length!==1)throw Error("expected exactly one matching claim file");
  return {source:{file,sha256:hash(source)},producer,
    functions:files[0].functions.map(f=>({name:f.name,namePos:f.namePos,
      ...(f.collection ? {collection:f.collection} : {}),
      unavailableTypes:unavailableTypes(f),
      signature:{params:f.params,retType:f.retType},
      entries:f.envs.map(e=>({pos:e.pos,bindings:e.vars.map(v=>({name:v.name,type:typeText(v.type),raw:v.type}))})),
      expressions:f.exprs.map(e=>({pos:e.pos,type:typeText(e.type),raw:e.type}))}))};
}

// Labels index the document's own type table; the first four rows are the
// primitives null, true, false and undefined.
function fromSourceClaims(
  source: string,
  file: string,
  input: SourceClaims,
  producer: string,
  // The Fragment's type parameters, where the caller read them. A source
  // outside the fragment has none, and its claims name none either.
  scopes: RigidScopes = new Map(),
): DraftReport {
  if(input.file!==file||input.sourceSha256!==hash(source))
    throw Error("source-claim source identity mismatch");
  const types=input.types;
  if(!Array.isArray(types)||types.length<4)throw Error("invalid source type table");
  const type=(A: import("./source-claims.mts").ClaimType):string=> {
    if(!Array.isArray(A)) {
      if("unavailable" in A && Object.keys(A).length===1 && typeof A.unavailable==="string" && A.unavailable)return "(unavailable)";
      if("array" in A) return `Array<${type(A.array)}>`;
      if("union" in A) return A.union.map(t => `(${type(t)})`).join(" | ");
      if("scheme" in A) {
        const s=A.scheme;
        if(!Array.isArray(s.typeParams)||!Array.isArray(s.params))throw Error("invalid quantified callable claim");
        const binders=s.typeParams.map(p=>{
          if(!p||typeof p.name!=="string"||!p.name)throw Error("invalid quantified callable binder");
          return p.name+(p.bound===null?"":` extends ${type(p.bound)}`);
        }).join(", ");
        // With no binders of its own this is a callable over an enclosing
        // binder, such as a returned `() => T`; it prints without a prefix.
        const prefix=s.typeParams.length?`<${binders}>`:"";
        // A receiver-indifferent scheme shows no `this`.
        const receiver=type(s.this);
        return `${prefix}(${[...(receiver==="unknown"?[]:[`this: ${receiver}`]), ...s.params.map((p,i)=>`arg${i}: ${type(p)}`), ...(s.rest === null ? [] : [`...rest: Array<${type(s.rest)}>`])].join(", ")}) => ${type(s.result)}`;
      }
      if(!("param" in A))throw Error("invalid source claim type");
      if(Object.keys(A).join()!=="param" || typeof A.param!=="string" || !A.param)throw Error("invalid rigid parameter claim");
      return A.param;
    }
    if(!Array.isArray(A)||A.some((i,k)=>!Number.isInteger(i)||i<0||i>=types.length||(k&&A[k-1]>=i)))throw Error("invalid source type labels");
    return obligationReader.typeText(types,A);
  };
  // Each function's own parameters, so a claim of `T` is drawn with what the
  // source says `T` is. Set per function below, before its points are built.
  let scope: RigidParameter[]=[];
  const rigid=(b: Point)=> {
    const named=rigidOf(b.type,scope);
    return named.length ? {rigid:named} : {};
  };
  const point=(b: Point)=> {
    if(!Object.hasOwn(b,"current"))throw Error("every source-claim point requires an explicit current field");
    const ordinary=type(b.type);
    if(b.current==null)return {type:ordinary,raw:b.type,...rigid(b)};
    if(!Array.isArray(b.current)||!b.current.length||b.current.some((f)=>
        !Array.isArray(f)||f.length!==2||typeof f[0]!=="string"||
        !Array.isArray(f[1])||f[1].some((i)=>!Number.isInteger(i)||i<0)))
      throw Error("invalid current-content assertion");
    if(!Array.isArray(b.type))throw Error("rigid parameters cannot carry current contents");
    const lifted=surface.lift(types,b.type,b.current);
    if(!lifted)throw Error("invalid current-content assertion");
    return {type:surface.printType(lifted).text,raw:{type:b.type,current:b.current},...rigid(b)};
  };
  const parameter=(b: NamedPoint)=> {
    if(b.current!=null)throw Error("function parameters cannot carry current-content assertions");
    return {name:b.name,type:point(b).type};
  };
  // The result is claimed by the function rather than at a point, so its
  // parameters are read from the same claim the result text is printed from.
  const resultRigid=(A: import("./source-claims.mts").ClaimType)=>rigidOf(A,scope);
  const sf=parse(source,file),entries=new Map<number, number>();
  const walk=(n: ts.Node)=>{if(ts.isStatement(n))entries.set(n.getStart(sf),n.end);n.forEachChild(walk);};walk(sf);
  // The module initialization is a unit like a function: no name, the span of
  // the top-level code, no parameters, and `undefined` as its completion.
  const initCode=sf.statements.filter(n=>ts.isExpressionStatement(n)||ts.isVariableStatement(n));
  const first=initCode[0], last=initCode[initCode.length-1];
  if(!!input.init!==!!first)throw Error("module initialization claims do not match the source");
  const units=[...input.functions,...(input.init&&first&&last?[{name:"",namePos:[first.getStart(sf),last.end] as Span,
    params:[],result:[3],entries:input.init.entries,expressions:input.init.expressions}]:[])];
  return {source:{file,sha256:input.sourceSha256},producer,
    functions:units.map(f=>{
      scope=scopeOf(scopes,f.namePos);
      return {name:f.name,namePos:f.namePos,
      ...(scope.length?{typeParams:scope}:{}),
      signature:{params:f.params.map(parameter),retType:type(f.result),
        ...(resultRigid(f.result).length?{resultRigid:resultRigid(f.result)}:{})},
      entries:f.entries.map(e=> {
        const end=entries.get(e.start);
        if(end===undefined)throw Error("source entry claim is not attached to a statement");
        return {pos:[e.start,end],bindings:e.bindings.map(b=>({name:b.name,...point(b)}))};
      }),expressions:f.expressions.map(e=>({pos:e.pos,...point(e)}))};
    })};
}

function attachConversion(
  source: string,
  report: ReportInput,
  sidecarBytes: string,
  conversion: ConversionManifest,
): ReportInput {
  if(conversion.kind!=="skjs-source-claim-conversion")throw Error("unsupported conversion manifest");
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
      const site=omission.site;
      if(typeof site!=="object" || site.kind!=="expression" || !site.pos)continue;
      const pos=site.pos;
      if(old.expressions.some(e=>JSON.stringify(e.pos)===JSON.stringify(pos)) &&
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
function parse(source: string, file: string) {
  return fragmentParse.openText(path.resolve(file), source);
}
/**
 * `identity` carries the report-level fingerprints and edit records into the
 * header comment and, where present, into the gap annotations.
 */
function render(
  source: string,
  report: ReportInput,
  results: { status: string; detail?: string }[] | null = null,
  identity: ReportIdentity = {},
): string {
  if(report.source?.sha256!==hash(source))throw Error("report source fingerprint mismatch");
  if(typeof report.producer!=="string" || !report.producer || !Array.isArray(report.functions))throw Error("invalid report header");
  if(results && results.length!==report.functions.length)throw Error("result count mismatch");
  const scanner=createScanner(false,undefined,source);
  for(let k=scanner.scan();k!==ts.SyntaxKind.EndOfFile;k=scanner.scan())
    if((k===ts.SyntaxKind.MultiLineCommentTrivia || k===ts.SyntaxKind.SingleLineCommentTrivia) &&
       /@verify-report\b/.test(scanner.getTokenText()))throw Error("source already contains report annotations; use the original source");
  const sf=parse(source,report.source.file), functions=new Map<string, ts.FunctionDeclaration>(),
    starts=new Set<number>(), spans=new Set<string>();
  function walk(n: ts.Node) {
    starts.add(n.getStart(sf));spans.add(`${n.getStart(sf)}:${n.end}`);
    if(ts.isFunctionDeclaration(n)&&n.name)functions.set(`${n.name.getStart(sf)}:${n.name.end}`,n);
    n.forEachChild(walk);
  }
  walk(sf);
  const insertions=new Map<number, string>(), seen=new Set<string>();
  function add(pos: number, data: Annotation){insertions.set(pos,(insertions.get(pos)||"")+comment(data));}
  // Ids are positional and deterministic, so the manifest and the annotations
  // agree without either having to re-derive spans.
  const idOf=(kind: string, i: number, j: number|null=null)=>kind==="function" ? `f${i}` : kind==="gap" ? `g${i}` : `f${i}${kind==="entry"?"e":"x"}${j}`;
  const checkSpan = (p: number[]) => {
    if(!Array.isArray(p)||p.length!==2||!p.every(Number.isSafeInteger)||p[0]<0||p[0]>=p[1]||p[1]>source.length)
      throw Error("invalid source span");
  };
  // The module initialization unit has no declaration of its own: it is the
  // file's top-level code, from its first statement to its last.
  const initCode=sf.statements.filter(n=>ts.isExpressionStatement(n)||ts.isVariableStatement(n));
  const initSpan=initCode.length ? [initCode[0]!.getStart(sf),initCode[initCode.length-1]!.end] : null;
  for(const [index,f] of report.functions.entries()) {
    checkSpan(f.namePos);
    const key=f.namePos.join(":"), declared=functions.get(key);
    const isInit=f.name==="" && !!initSpan && initSpan.join(":")===key;
    if((!isInit && (!declared || declared.name?.text!==f.name)) || seen.has(`fn:${key}`))
      throw Error("missing or duplicate function identity");
    const start=isInit ? f.namePos[0] : declared!.getStart(sf), end=isInit ? f.namePos[1] : declared!.end;
    seen.add(`fn:${key}`);
    if(!Array.isArray(f.entries)||!Array.isArray(f.expressions))throw Error("invalid function claims");
    add(start,{kind:"function",id:idOf("function",index),name:f.name,producer:report.producer,
      collection:f.collection,collectionSource:f.collectionSource,
      ...(f.signature ? {signature:f.signature} : {}),
      ...(results ? {verification:results[index]} : {verification:{status:"not-run"}})});
    const at=(kind: string, q: { pos: number[] })=> {
      checkSpan(q.pos);
      if(q.pos[0]<start||q.pos[1]>end||!starts.has(q.pos[0]) ||
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
        unsupported:q.bindings.filter(b=>isRecord(b.raw)&&b.raw.unsupported).map(b=>b.name),status:"producer-claim"});
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
  const header=comment({kind:"report",source:report.source,producer:report.producer,
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
function tokens(text: string) {
  const scanner=createScanner(true,undefined,text), out=[];
  for(let k=scanner.scan();k!==ts.SyntaxKind.EndOfFile;k=scanner.scan())out.push([k,scanner.getTokenText()]);
  return out;
}
const shape=(n: ts.Node): [number, unknown[]]=>{const kids: unknown[]=[];n.forEachChild(c=>{kids.push(shape(c));});return [n.kind,kids];};

// Absence is meaningful only when the producer explicitly records collection progress.
function coverage(source: string, report: ReportInput) {
  const sf=parse(source,report.source.file), gaps=[];
  for(const node of sf.statements) {
    if(!ts.isFunctionDeclaration(node)||!node.name||!node.body)continue;
    // Bound so the guard above is visible to the closure below.
    const named=node.name;
    const f=report.functions.find(f=>f.namePos[0]===named.getStart(sf)&&f.namePos[1]===named.end);
    if(!f){gaps.push({pos:[node.getStart(sf),node.end],status:"claims unavailable; verification not established"});continue;}
    const snapshot=f.collectionSnapshot||f;
    for(const gap of f.conversionGaps||[])gaps.push(gap);
    if(!f.collection)continue;
    for(const pos of f.collection.visitedExpressions||[]) {
      if(!snapshot.expressions.some(e=>e.pos[0]===pos[0]&&e.pos[1]===pos[1])) {
        if(!Array.isArray(pos)||pos.length!==2||!pos.every(Number.isSafeInteger)||pos[0]<node.getStart(sf)||pos[1]>node.end||pos[0]>=pos[1])throw Error("invalid expression visit span");
        const matches=(n: ts.Node): boolean|undefined=>(n.getStart(sf)===pos[0]&&n.end===pos[1])||n.forEachChild(matches);
        if(!matches(node))throw Error("cannot attach expression visit");
        gaps.push({pos,status:"expression entered without a type result"});
      }
    }
    if(f.collection.completion==="aborted") {
      const walk=(n: ts.Node)=> {
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
const canonical = (x: unknown) => JSON.stringify(normalize(x));
function normalize(x: unknown): unknown {
  if(isList(x))return x.map(normalize);
  if(isRecord(x))return Object.fromEntries(Object.keys(x).sort().map(k=>[k,normalize(x[k])]));
  return x;
}
function compareClaims(source: string, baseline: ReportInput, current: ReportInput) {
  if(baseline.source?.file!==current.source?.file)throw Error("baseline source identity mismatch");
  render(source,baseline);render(source,current); // Includes exact source digest and attachment validation.
  const sites=(report: ReportInput)=> {
    const out=new Map();
    for(const f of report.functions) {
      const put=(kind: string, span: number[], value: unknown)=>out.set(`${f.namePos.join(":")}:${kind}:${kind==="entry"?span[0]:span.join(":")}`,
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

/** The declaration a reported function names. `render` above matched every one
 * of them, so failing here is that having stopped being true. */
function declaring(nodes: ts.FunctionDeclaration[], start: number): ts.FunctionDeclaration {
  const found=nodes.find(n=>n.name?.getStart()===start);
  if(!found)throw Error("no declaration for a reported function");
  return found;
}

function run(executable: string, args: string[]) {
  const r=spawnSync(executable,args,{encoding:"utf8",timeout:120000,maxBuffer:32*1024*1024});
  if(r.error || r.signal)throw Error(`tool execution failed: ${r.error?.message || r.signal}`);
  return r;
}

// `--format source-claims` hands one normalized sidecar; SKJS hands the list of
// files this run selects from. `fromSkjs` and `fromSourceClaims` have already
// rejected a document that is not the shape its format names.
const isFileList=(d: SkjsFile[] | SourceClaims): d is SkjsFile[] => Array.isArray(d);
function verifySkjs(
  sourcePath: string,
  source: string,
  claims: SkjsFile[] | SourceClaims,
  file: string,
  // Only the function identities are read here. Writing that types the results
  // this returns as the reader's own `Result`, minus the `function` id `main`
  // attaches afterwards.
  report: { functions: { name: string; namePos: number[] }[] },
  verifier: string,
  depth: number,
  normalized = false,
  tsconfigPath?: string,
) {
  const temp=fs.mkdtempSync(path.join(os.tmpdir(),"annotated-source-"));
  try {
    // Called rather than spawned: a node start costs more than the parse, and
    // this runs once per source. The front end is not hashed: no verdict
    // depends on which tool produced the request, only on the request and the
    // evidence, and the source fingerprint already ties both to these bytes.
    const identity={verifierSha256:hash(fs.readFileSync(verifier))};
    let ast;
    try {
      ast=fragmentParse.parseFile(sourcePath,false,tsconfigPath);
    } catch(error) {
      const detail=messageOf(error);
      if(!detail.startsWith("gate:"))throw Error(`source parser failed: ${detail}`);
      return {identity,results:report.functions.map((): FunctionResult=>({status:"unsupported",detail:detail.trim()}))};
    }
    ast.file=file;
    // Whole file first. The per-function pass below exists to attribute a
    // failure to the function it belongs to; when nothing fails there is
    // nothing to attribute, and one produce/check covers every function in the
    // file. That is the same evidence, from the same two commands, at two
    // processes instead of two per function.
    const whole=(()=>{
      const document=clone(claims);
      const c=isFileList(document) ? document.filter(g=>g.file===file) : document;
      if(isFileList(c)) {
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
      return report.functions.map((): FunctionResult=>({status:"verified",scope:"modeled function and required claims",certificateSha256}));
    })();
    if(whole) {
      if(fs.readFileSync(sourcePath,"utf8")!==source)throw Error("source changed during verification");
      return {identity,results:whole};
    }
    const results=report.functions.map((f): FunctionResult=> {
      const named=(g: { name: string; namePos: Span })=>g.name===f.name && JSON.stringify(g.namePos)===JSON.stringify(f.namePos);
      // The whole tree goes to the verifier: the other functions are this
      // one's module, reached at their signatures. Only its claims are sent.
      const a=ast;
      // The initialization unit is the tree's top-level code, not a function.
      if(f.name==="" ? !a.init?.length : a.functions.filter(named).length!==1)
        throw Error("function identity mismatch during verification");
      const only=["--function",f.name,String(f.namePos[0]),String(f.namePos[1])];
      const document=clone(claims);
      const c=isFileList(document) ? document.filter(g=>g.file===file) : document;
      let refusals: Unavailable[]=[];
      if(isFileList(c)) {
        const selected=c[0];
        selected.functions=selected.functions.filter(named);
        refusals=unavailableTypes(selected.functions[0]);
        // Metadata is for reporting only, excluded from verifier input and its digest.
        for(const g of selected.functions)delete g.unavailableTypes;
      } else c.functions=c.functions.filter(named);
      const ap=path.join(temp,"ast.json"), cp=path.join(temp,"claims.json"), ep=path.join(temp,"evidence.json");
      fs.writeFileSync(ap,JSON.stringify(a));fs.writeFileSync(cp,JSON.stringify(c));
      const produced=run(verifier,[normalized?"--produce-source-claims":"--produce-stateful-source",ap,cp,file,ep,String(depth),...only]);
      if(produced.status!==0) {
        const rawDetail=(produced.stderr||produced.stdout).trim();
        const diagnostic=readDiagnostic(rawDetail);
        const detail=diagnostic ? rawDetail.split("\nobligation-diagnostic: ")[0] : rawDetail;
        const direct=diagnostic?.kind==="direct-obligation" ? diagnostic : null;
        const sourceRefusal=diagnostic?.kind==="source-refusal" ? diagnostic : null;
        const located=/^(?:reject: )?(source expression obligation|closure expression claim|source incoming edge obligation|unsupported source expression) at \[(\d+),(\d+)\):/.exec(detail);
        const genericPoint=/^(?:reject: )?generic (entry claim|expression claim|return contract|binding annotation) at \[(\d+),(\d+)\):/.exec(detail);
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
        const outsideFragment=/outside the [^:]*fragment\.?$/.test(detail);
        const location: Failure|null=direct ? (direct.sourceMap.role==="entry-claim" ? {kind:"environment-obligation",start:direct.sourceMap.pos[0]} : direct.sourceMap.role==="expression-claim" ? {kind:"expression-obligation",pos:direct.sourceMap.pos} : {kind:"direct-obligation",pos:direct.sourceMap.pos}) : sourceRefusal ? {kind:"source-limitation",pos:sourceRefusal.sourceMap.pos,reason:sourceRefusal.reason} : genericPoint ? (genericPoint[1]==="entry claim" ?
          {kind:"environment-obligation",start:Number(genericPoint[2])} :
          {kind:"expression-obligation",pos:[Number(genericPoint[2]),Number(genericPoint[3])]}) : parameterClaim ? {kind:"parameter-claim",binding:parameterClaim[1]} : unavailableType ? {kind:"unavailable-type-claim",
          ...(unavailableBinding ? {start:Number(environment[1]),binding:unavailableBinding[1]} :
            located ? {pos:[Number(located[2]),Number(located[3])]} : {})} : nonInvariant ? {kind:"source-limitation",reason:"non-invariant-cell-contract",
          ...(environment ? {start:Number(environment[1])} : located ? {pos:[Number(located[2]),Number(located[3])]} : {})} : located ? {kind:located[1]==="unsupported source expression" ? "source-limitation" : located[1]==="source incoming edge obligation" ? "edge-obligation" : "expression-obligation",pos:[Number(located[2]),Number(located[3])]} :
          absentExpr ? {kind:"missing-expression-claim",pos:[Number(absentExpr[1]),Number(absentExpr[2])]} :
          absentEnv ? {kind:"missing-environment-claim",start:Number(environment[1])} :
          absentBinding ? {kind:"missing-environment-claim",start:Number(environment[1]),binding:absentBinding[1]} :
          environment ? {kind:"environment-obligation",start:Number(environment[1])} :
          outsideFragment ? {kind:"source-limitation"} : null;

        // One shape for every branch above, which is the reader's own
        // `Failure`: a place (a span or an entry start), the binding it
        // concerns where there is one, and the producer's own reason where the
        // refusals below match it.
        if(unavailableType && location) {
          const matches=refusals.filter(d=>unavailableBinding ?
            d.kind==="entry"&&d.pos?.[0]===location.start&&d.binding===location.binding :
            located ? d.kind==="expression"&&JSON.stringify(d.pos)===JSON.stringify(location.pos) : false);
          if(matches.length===1)location.reason=matches[0].reason;
        }
        // Bind node-local IDs to this exact function, source, and selected
        // claims. A span in a diagnostic's request is a pair, which `render`
        // has already checked this one to be.
        const namePos: Span=[f.namePos[0],f.namePos[1]];
        const obligation=diagnostic ? {...diagnostic,input:{file,functionName:f.name,
          namePos,sourceSha256:hash(source),claimsSha256:hash(JSON.stringify(c))}} : null;
        if(!location)throw Error(`verifier returned an unlocated failure for ${f.name}: ${detail}`);
        return {status:"not-established",detail,...((sourceRefusal || unavailableType || nonInvariant) ? {stage:"source-extraction"} : {}),location,
          ...(obligation ? {obligation, obligationView: presentObligation(obligation, source)} : {})};
      }
      const checked=run(verifier,[normalized?"--check-source-claims":"--check-stateful-source",ap,cp,file,ep,...only]);
      if(checked.status!==0) {
        // Evidence production may expose proved graph consequences while final
        // acceptance still refuses a source-plan variant whose semantic
        // certificate is missing. Preserve that located refusal as the result;
        // the existence of the graph bundle must never promote it to verified.
        const rawDetail=(checked.stderr||checked.stdout).trim();
        const diagnostic=readDiagnostic(rawDetail);
        if(diagnostic?.kind!=="source-refusal")
          throw Error(`independent certificate check failed for ${f.name}: ${rawDetail}`);
        const detail=rawDetail.split("\nobligation-diagnostic: ")[0];
        const namePos: Span=[f.namePos[0],f.namePos[1]];
        const obligation={...diagnostic,input:{file,functionName:f.name,namePos,
          sourceSha256:hash(source),claimsSha256:hash(JSON.stringify(c))}};
        return {status:"not-established",detail,stage:"source-extraction",
          location:{kind:"source-limitation",pos:diagnostic.sourceMap.pos,reason:diagnostic.reason},
          obligation,obligationView:presentObligation(obligation,source)};
      }
      return {status:"verified",scope:"modeled function and required claims",certificateSha256:hash(fs.readFileSync(ep))};
    });
    if(fs.readFileSync(sourcePath,"utf8")!==source)throw Error("source changed during verification");
    return {identity,results};
  } finally {fs.rmSync(temp,{recursive:true,force:true});}
}

function checkFresh(output: string) {
  const m=JSON.parse(fs.readFileSync(output+".json","utf8"));
  const checks=[[output,m.annotatedSha256],[m.sourcePath,m.source.sha256],[m.claimsPath,m.claimsSha256]];
  if(m.conversionPath)checks.push([m.conversionPath,m.conversionSha256]);
  if(m.baselinePath)checks.push([m.baselinePath,m.baselineSha256]);
  if(m.diagnosticsPath)checks.push([m.diagnosticsPath,m.diagnosticsSha256]);
  if(m.verifierPath)checks.push([m.verifierPath,m.verifierSha256]);
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
const namedBinding=(name: string, typeNode: ts.TypeNode | undefined)=>{
  let type=null;
  try{type=typeNode?claimOfTerm(fragmentParse.typeOf(typeNode)):null;}catch(e){type=null;}
  return {name,type};
};
// A declaration the surface names with a plain identifier; a binding pattern
// binds no single name a claim could be about.
const namedDeclaration=<T extends { name: ts.BindingName }>(p: T): p is T & { name: ts.Identifier }=>
  ts.isIdentifier(p.name);
const identifiers=(nodes: readonly (ts.ParameterDeclaration|ts.VariableDeclaration)[] | undefined): [string, ts.TypeNode|undefined][]=>
  (nodes||[]).filter(namedDeclaration).map(p=>[p.name.text,p.type]);
const declaredBy=(n: ts.Node)=>ts.isVariableStatement(n)?identifiers(n.declarationList.declarations):[];

// TypeScript's own "is this node in expression position" test is not part of
// the public surface, and kind alone is not it: the name a declaration binds
// is an Identifier like any other. The name a node *declares* is always its
// `name` child — with one exception, a property access, whose `.value` is not
// a declared name but part of the expression, and carries a claim like any
// other site.
const isDeclaredName = (n: ts.Node) => {
  const p=n.parent;
  return !!p && "name" in p && p.name===n && !ts.isPropertyAccessExpression(p);
};
const isExpressionNode = (n: ts.Node) => ts.isExpression(n) && !isDeclaredName(n);

/** The claim sites a unit's claims leave out: a function's body under its
 * parameters, or the module's top-level code, read in order under nothing. */
function missingClaimSites(unit: ts.FunctionDeclaration | readonly ts.Statement[], f: { entries: { pos: number[] }[]; expressions: { pos: number[] }[] }) {
  const sites: { kind: string; pos: number[]; syntax: string; bindings?: unknown[] }[]=[];
  const walk=(n: ts.Node, scope: [string, ts.TypeNode|undefined][])=> {
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
  if(Array.isArray(unit)) {
    let inner: [string, ts.TypeNode|undefined][]=[];
    for(const st of unit as readonly ts.Statement[]) { walk(st,inner); inner=inner.concat(declaredBy(st)); }
  } else {
    const node=unit as ts.FunctionDeclaration;
    if(node.body) walk(node.body,identifiers(node.parameters));
  }
  return sites.sort((a,b)=>a.pos[0]-b.pos[0]||a.pos[1]-b.pos[1]);
}

export function main(args: string[]) {
  if(args[0]==="--check-fresh" && args.length===2)return checkFresh(args[1]);
  const sourcePath=args.shift();
  // Every switch in `allowed` below lands here, so the record says so once
  // rather than growing a property at a time.
  const options: {
    format:string, depth:string|number, claims?:string, out?:string, verify?:string,
    producer?:string, "file-key"?:string, diagnostics?:string, baseline?:string,
    conversion?:string, stdout?:string, project?:string,
  } = {format:"skjs",depth:10};
  if(!sourcePath)throw Error("usage: annotate-source.mts source.ts --claims claims.json [--out annotated.ts] [--verify verifier] [--format report --producer name]");
  const allowed=new Set(["claims","out","verify","format","producer","file-key","depth","diagnostics","baseline","conversion","stdout","project"]);
  // The switch names a field of the record above; nothing else can be written.
  const isOption=(k: string): k is keyof typeof options => allowed.has(k);
  while(args.length) {
    const key=args.shift()?.replace(/^--/,"");
    const value=args.shift();
    if(!key||!isOption(key)||value===undefined)throw Error(`invalid option ${key}`);
    options[key]=value;
  }
  options.producer ??= options.conversion ? "skjs (converted)" : options.format==="skjs" ? "skjs" : "unspecified";
  if(!options.claims || !["skjs","report","source-claims"].includes(options.format))throw Error("expected --claims and a supported format");
  if(!/^\d+$/.test(String(options.depth))||!Number.isSafeInteger(Number(options.depth)))throw Error("invalid proof depth");
  if(options.format==="report"&&options.verify)throw Error("verification of generic report inputs needs a producer adapter; stored statuses are never trusted");
  const output=options.out || sourcePath.replace(/\.ts$/,"")+".annotated.ts", manifest=output+".json";
  if([sourcePath,options.claims,options.verify].filter((p): p is string=>!!p).some(p=>path.resolve(p)===path.resolve(output)))throw Error("output must differ from inputs");
  // Nothing is written in stdout mode, so an existing report there is not a conflict.
  if(options.stdout!=="json" && (fs.existsSync(output)||fs.existsSync(manifest)))throw Error("output already exists; choose a new --out path");
  const source=fs.readFileSync(sourcePath,"utf8"), bytes=fs.readFileSync(options.claims,"utf8");
  const read=JSON.parse(bytes);
  // A kept draft is a candidate: the claims with the format and the source they
  // are about wrapped around them. The reader writes one beside its source, and
  // it names everything `--format` would have had to be told, so it is taken
  // from the file rather than asked for again.
  const wrapped=read && !Array.isArray(read) && typeof read.format==="string" && "claims" in read;
  if(wrapped) {
    if(read.file!==sourcePath && read.file!==options["file-key"])
      throw Error(`that candidate is about ${read.file}`);
    if(read.sourceSha256!==hash(source))
      throw Error("that candidate is about this source as it was before it changed");
    options.format=read.format;
  }
  const input=wrapped ? read.claims : read;
  const file=options["file-key"] || sourcePath;
  const tsconfigPath=options.project ? tsconfigOf(options.project) : undefined;
  // The bound of a rigid parameter is written in the source and nowhere in the
  // claims, so it is read from the Fragment here, once, and printed into the
  // report. A source the parser refuses declares no parameters to read: the
  // report is still a report, so this is not the place to fail over it.
  let scopes: RigidScopes=new Map();
  try {scopes=rigidScopes(fragmentParse.parseFile(sourcePath,false,tsconfigPath));}
  catch {scopes=new Map();}
  let report: ReportInput=options.format==="skjs" ? fromSkjs(source,file,input,options.producer) : options.format==="source-claims" ? fromSourceClaims(source,file,input,options.producer,scopes) : input;
  let conversion: ConversionManifest|null=null,conversionBytes=null;
  if(options.conversion) {
    if(options.format!=="source-claims")throw Error("--conversion requires --format source-claims");
    conversionBytes=fs.readFileSync(options.conversion,"utf8");
    const manifest: ConversionManifest=JSON.parse(conversionBytes);
    conversion=manifest;
    report=attachConversion(source,report,bytes,manifest);
  }
  // Validate attachment before running any expensive proof generation.
  render(source,report);
  // The fields this file reads of a verifier result; the manifest carries
  // whatever else the verifier recorded, unchanged.
  let results: { status: string; detail?: string }[]|null=null, comparison=null;
  let identity: ReportIdentity = {claimsSha256:hash(bytes)};
  if(conversion&&conversionBytes!==null)identity.conversionSha256=hash(conversionBytes);
  if(options.baseline) {
    const baselineBytes=fs.readFileSync(options.baseline,"utf8");
    comparison=compareClaims(source,JSON.parse(baselineBytes),report);
    identity.baselineSha256=hash(baselineBytes);
  }
  if(options.verify) {
    const verified=verifySkjs(sourcePath,source,input,file,report,path.resolve(options.verify),Number(options.depth),options.format==="source-claims",tsconfigPath);
    results=verified.results;identity={...identity,...verified.identity};
  }
  const diagnostics=options.diagnostics ? fs.readFileSync(options.diagnostics,"utf8") : null;
  if(diagnostics!==null)identity.diagnosticsSha256=hash(diagnostics);
  const annotated=render(source,report,results,{...identity,...(comparison?{claimChanges:comparison.changes}:{}),...(conversion?{conversionOmissions:conversion.omissions}:{})});
  const sourceFile=parse(source,report.source.file);
  const functionNodes=sourceFile.statements.filter(ts.isFunctionDeclaration);
  const data={sourcePath:path.resolve(sourcePath),claimsPath:path.resolve(options.claims),
    ...(options.verify ? {verifierPath:path.resolve(options.verify)} : {}),
    ...identity,source:report.source,annotatedSha256:hash(annotated),producer:report.producer,
    ...(options.diagnostics ? {diagnosticsPath:path.resolve(options.diagnostics),diagnostics} : {}),
    ...(conversion&&options.conversion?{conversionPath:path.resolve(options.conversion),conversion}:{}),
    ...(comparison&&options.baseline?{baselinePath:path.resolve(options.baseline),comparison}:{}),
    // A declaration the report says nothing about: named, so the reader can
    // offer its contract. One without a name or a body is not a declaration
    // this report is about.
    missingFunctions:functionNodes.flatMap(n=>{
      const name=n.name;
      if(!name||!n.body||report.functions.some(f=>f.namePos[0]===name.getStart()))return [];
      return [{name:name.text,namePos:[name.getStart(),name.end],pos:[n.getStart(),n.end],
        parameters:n.parameters.map(p=>p.name.getText()),missingSites:missingClaimSites(n,{entries:[],expressions:[]})}];
    }),
    gaps:coverage(source,report),
    functions:report.functions.map((f,i)=>({id:`f${i}`,...f,
      // The declared result's annotation, where the source writes one: the reader
      // shows the claimed result there, and a return contract points at it.
      // The initialization unit spans the module's top-level code and has no
      // declared result.
      ...(f.name==="" ? {pos:f.namePos,resultPos:null,
          missingSites:missingClaimSites(sourceFile.statements.filter(n=>ts.isExpressionStatement(n)||ts.isVariableStatement(n)),f)} :
        ((node: ts.FunctionDeclaration)=>({pos:[node.getStart(),node.end],resultPos:node.type ? [node.type.getStart(),node.type.end] : null,missingSites:missingClaimSites(node,f)}))(
        declaring(functionNodes,f.namePos[0]))),
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
export {hash,typeText,fromSkjs,fromSourceClaims,attachConversion,render,coverage,compareClaims,verifySkjs};
/* The intermediate a converter builds and `render` writes out. It is this
 * file's own shape rather than a language of its own, and is exported so a
 * suite that alters one says which document it is altering. */
export type {DraftReport, ReportInput};
if(process.argv[1] && import.meta.filename===path.resolve(process.argv[1]))
  try {main(process.argv.slice(2));}catch(e){console.error(messageOf(e));process.exitCode=1;}
