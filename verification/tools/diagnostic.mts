import { decodeGraph, decodeLabels, type TypeGraph, type Labels, type Clause } from "./type-graph.mts";
import { decodeTerm, isTag, type Tag, type Term } from "./calculus.mts";
import { decodeNode, type ProgramNode } from "./control-flow.mts";
import type { Span } from "./span.mts";

// Optional explanatory metadata, never evidence. A record this reader cannot
// decode field by field is left in the human diagnostic; it must not change the
// verification outcome.

/** Where the verifier stopped. */
export type Phase = "proof-search" | "certificate-check" | "request-validation";

/** What it stopped on. */
export type Kind =
  | "node-typing"
  | "edge-coverage"
  | "expression-claim"
  | "direct-obligation"
  | "source-refusal"
  | "production-failure";

/**
 * Where a node the failure names sits, in the source the request came from.
 * Absent when the request carried no source map.
 */
export interface SourceMapEntry {
  pos: Span;
  role: string;
  environmentStart: number | null;
  context: {name: string; span: Span | null}[];
}

/** The judgement a failure could not establish. */
export interface Sequent {
  context: Labels[];
  term: Term;
  type: Labels;
}

/** An assertion about a runtime slot: for a cell, about the named field of the
 * object it holds; for a value, about the slot itself, where the field is not
 * consulted. */
export type HeapAtom = "nul" | "undef" | "tru" | "fls" | "num" | "str" |
  Extract<Clause, {numLit: unknown} | {strLit: unknown}>;
const HEAP_ATOMS: Record<Extract<HeapAtom, string>, true> = {
  nul: true, undef: true, tru: true, fls: true, num: true, str: true,
};
const heapAtoms: readonly unknown[] = Object.keys(HEAP_ATOMS);
function heapAtom(v: unknown): void {
  if (heapAtoms.includes(v)) return;
  // Singleton payloads use the graph language's existing decoder.
  if (typeof v === "object" && v !== null && "strLit" in v) {
    decodeGraph([[{strLit: record(v,["strLit"]).strLit}]]);
    return;
  }
  const a = record(v,["numLit"]);
  decodeGraph([[{numLit: a.numLit}]]);
}
export interface HeapFact {
  slot: number;
  contents: HeapAtom[];
  field: string;
}
export interface HeapKnowledge {
  cells: HeapFact[]; values: HeapFact[];
  /** A read link (`alias` false), a value equality (`alias` true), or, with
   * `distinct`, two fields at different locations: `cell.field` and
   * `value.other`. */
  links: {cell: number; value: number; alias: boolean; field: string; distinct: boolean; other: string}[];
}

/** A node of the certificate graph, as the failure reports it. */
export interface DiagnosticNode {
  label: number;
  sourceMap: SourceMapEntry | null;
  node: ProgramNode | null;
  claim: { context: Labels[]; type: Labels } | null;
  requiredKnowledge: HeapKnowledge | null;
}

/**
 * What an edge carries from its source to its destination, mirroring the
 * continuation the source node ends in (RequestJson.lean, `failureDiagnostic`).
 */
export interface DiagnosticTransfer {
  available: Labels[];
  target: { label: number; mapping: number[] | null };
  /** Which way a two-armed Boolean test went; null for every other edge. */
  booleanObservation: boolean | null;
  /** The tag test an edge answers, where the continuation is one. */
  tagObservation: { test: Tag; answer: boolean; slot: number } | null;
}

/** What every record carries, whatever the failure was. */
interface Common {
  phase: Phase;
  outcome: "not-established";
  /** The proof budget the search was given. */
  fuel: number;
  types: TypeGraph;
  /**
   * The result type the request asked for. Absent from a closure expression
   * claim, which is produced without a request and so has none — not an
   * omission to paper over.
   */
  requiredResult?: Labels;
  /** Attached by the report writer, not by the verifier. */
  input?: {
    file: string;
    functionName: string;
    namePos: Span;
    sourceSha256: string;
    claimsSha256: string;
  };
}

/** A node of the certificate graph could not be typed. */
export interface NodeTyping extends Common {
  kind: "node-typing";
  id: string;
  source: DiagnosticNode;
  sequent: Sequent;
}

/** An edge's destination was not justified by what its source carries. */
export interface EdgeCoverage extends Common {
  kind: "edge-coverage";
  id: string;
  edgeIndex: number;
  source: DiagnosticNode;
  destination: DiagnosticNode;
  transfer: DiagnosticTransfer;
}

/**
 * A closure expression claim did not follow. This failure is raised where the
 * claim is rather than at a graph node, so it names its place directly instead
 * of hanging a source map under a node: see `sourceMap` above, and
 * ExpressionClaims.lean beside `failureDiagnostic` in RequestJson.lean.
 */
export interface ExpressionClaimFailure extends Common {
  kind: "expression-claim";
  id: string;
  sourceMap: SourceMapEntry;
  sequent: Sequent;
}

export type DirectType =
  | { kind: "rigid"; name: string }
  | { kind: "ground"; labels: Labels }
  /** Every value; the receiver of a signature indifferent to it. */
  | { kind: "top" }
  /** A callable whose signature mentions a rigid parameter, such as `() => T`,
   * with the receiver a call passes it. */
  | { kind: "arrow"; receiver: DirectType; params: DirectType[]; result: DirectType }
  | { kind: "array"; element: DirectType }
  | { kind: "variadic"; receiver: DirectType; params: DirectType[]; element: DirectType; result: DirectType };
export interface DirectParameter {
  name: string;
  scope: "ambient" | "quantified";
  upper: DirectType | null;
}
export interface DirectBinding { name: string; type: DirectType }
export type DirectSubject =
  | { kind: "binding"; name: string; pos: Span }
  | { kind: "expression"; pos: Span }
  | { kind: "return-value"; pos: Span }
  | { kind: "closure-body"; pos: Span };
export type DirectJudgment =
  | {
      kind: "subtyping";
      parameters: DirectParameter[];
      context: DirectBinding[];
      subject: DirectSubject;
      actual: DirectType;
      expected: DirectType;
    }
  | {
      kind: "scheme-introduction";
      parameters: DirectParameter[];
      context: DirectBinding[];
      body: Extract<DirectSubject, {kind: "closure-body"}>;
      actual: DirectType;
      expected: DirectType;
    };

// These records are compile-time exhaustiveness guards. Adding a wire variant
// to one of the unions requires naming it here and handling it in the total
// renderer; unknown input strings are still refused at runtime below.
const DIRECT_TYPE_KINDS = {rigid:true,ground:true,top:true,arrow:true,array:true,variadic:true} satisfies Record<DirectType["kind"],true>;
const DIRECT_SUBJECT_KINDS = {
  binding:true,expression:true,"return-value":true,"closure-body":true,
} satisfies Record<DirectSubject["kind"],true>;
const DIRECT_JUDGMENT_KINDS = {
  subtyping:true,"scheme-introduction":true,
} satisfies Record<DirectJudgment["kind"],true>;
const DIRECT_PARAMETER_SCOPES = {
  ambient:true,quantified:true,
} satisfies Record<DirectParameter["scope"],true>;
const isDirectParameterScope = (v: unknown): v is DirectParameter["scope"] =>
  typeof v === "string" && v in DIRECT_PARAMETER_SCOPES;

/** A direct source checker stopped on a judgment that is not an
 * ordinary ground graph sequent, such as rigid generic subtyping or universal
 * scheme introduction. Its source place is mandatory. */
export interface DirectObligationFailure extends Common {
  kind: "direct-obligation";
  id: string;
  sourceMap: SourceMapEntry;
  judgment: DirectJudgment;
}

/** Source conversion stopped before a semantic judgment existed. This is a
 * located refusal, never a sequent and never a failed proof. */
export interface SourceRefusal extends Common {
  kind: "source-refusal";
  id: string;
  sourceMap: SourceMapEntry;
  reason: string;
}

/** Something was produced and then rejected by the independent check. */
export interface ProductionFailure extends Common {
  kind: "production-failure";
  failure: string;
}

export type ObligationDiagnostic =
  | NodeTyping
  | EdgeCoverage
  | ExpressionClaimFailure
  | DirectObligationFailure
  | SourceRefusal
  | ProductionFailure;

const PHASES: readonly unknown[] = [
  "proof-search",
  "certificate-check",
  "request-validation",
];
const KINDS: readonly unknown[] = [
  "node-typing",
  "edge-coverage",
  "expression-claim",
  "direct-obligation",
  "source-refusal",
  "production-failure",
];
const PREFIX = "obligation-diagnostic: ";

const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
function record(v: unknown, required: string[], optional: string[] = []): Record<string, unknown> {
  if (!isRecord(v) || required.some(k => !(k in v)) || Object.keys(v).some(k => ![...required,...optional].includes(k))) throw Error("invalid diagnostic fields");
  return v;
}
function nat(v: unknown) { if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0) throw Error("invalid diagnostic index"); }
function span(v: unknown): asserts v is Span { if (!Array.isArray(v) || v.length !== 2) throw Error("invalid diagnostic span"); v.forEach(nat); if (v[1] < v[0]) throw Error("reversed span"); }
function sourceMap(v: unknown): asserts v is SourceMapEntry | null {
  if (v === null) return;
  const m = record(v,["pos","role","environmentStart","context"]);
  span(m.pos); if (typeof m.role !== "string") throw Error("invalid role");
  if (m.environmentStart !== null) nat(m.environmentStart);
  if (!Array.isArray(m.context)) throw Error("invalid source context");
  for (const entry of m.context) {
    const d = record(entry,["name","span"]);
    if (typeof d.name !== "string") throw Error("invalid binding name");
    if (d.span !== null) span(d.span);
  }
}

function directType(v: unknown, size: number, scope: ReadonlySet<string>): DirectType {
  const t = record(v,["kind"], ["name","labels","receiver","params","result","element"]);
  if (typeof t.kind !== "string" || !(t.kind in DIRECT_TYPE_KINDS))
    throw Error("unknown direct-obligation type");
  if (t.kind === "variadic") {
    record(v,["kind","receiver","params","element","result"]);
    if (!Array.isArray(t.params)) throw Error("invalid variadic parameters");
    return {kind:"variadic",receiver:directType(t.receiver,size,scope),params:t.params.map(p=>directType(p,size,scope)),
      element:directType(t.element,size,scope),result:directType(t.result,size,scope)};
  }
  if (t.kind === "top") {
    record(v,["kind"]);
    return {kind:"top"};
  }
  if (t.kind === "array") {
    record(v,["kind","element"]);
    return {kind:"array",element:directType(t.element,size,scope)};
  }
  if (t.element !== undefined) throw Error("unexpected direct-obligation element");
  if (t.kind === "rigid") {
    if (typeof t.name !== "string" || !scope.has(t.name) || t.labels !== undefined)
      throw Error("undeclared direct-obligation rigid type");
    return {kind:"rigid",name:t.name};
  }
  if (t.kind === "ground") {
    if (t.name !== undefined || t.receiver !== undefined || t.params !== undefined || t.result !== undefined)
      throw Error("invalid direct-obligation ground type");
    return {kind:"ground",labels:decodeLabels(t.labels,size)};
  }
  if (t.kind === "arrow") {
    record(v,["kind","receiver","params","result"]);
    if (!Array.isArray(t.params))
      throw Error("invalid direct-obligation arrow type");
    return {kind:"arrow",receiver:directType(t.receiver,size,scope),params:t.params.map((p) => directType(p,size,scope)),
      result:directType(t.result,size,scope)};
  }
  throw Error("unknown direct-obligation type");
}
function directSubject(v: unknown): DirectSubject {
  const s = record(v,["kind","pos"],["name"]); span(s.pos);
  if (typeof s.kind !== "string" || !(s.kind in DIRECT_SUBJECT_KINDS))
    throw Error("unknown direct-obligation subject");
  if (s.kind === "binding") {
    if (typeof s.name !== "string") throw Error("invalid direct-obligation binding");
    return {kind:"binding",name:s.name,pos:s.pos};
  }
  if (s.name !== undefined) throw Error("invalid direct-obligation subject name");
  if (s.kind === "expression" || s.kind === "return-value" || s.kind === "closure-body")
    return {kind:s.kind,pos:s.pos};
  throw Error("unknown direct-obligation subject");
}
function directJudgment(v: unknown, size: number): DirectJudgment {
  const j = record(v,["kind","parameters","context","actual","expected"],["subject","body"]);
  if (typeof j.kind !== "string" || !(j.kind in DIRECT_JUDGMENT_KINDS))
    throw Error("unknown direct-obligation judgment");
  if (!Array.isArray(j.parameters) || !Array.isArray(j.context))
    throw Error("invalid direct-obligation scope");
  const scope = new Set<string>();
  const rawParameters = j.parameters.map((raw) => {
    const p = record(raw,["name","scope","upper"]);
    if (typeof p.name !== "string" || !p.name || scope.has(p.name))
      throw Error("invalid direct-obligation parameter");
    if (!isDirectParameterScope(p.scope))
      throw Error("invalid direct-obligation parameter scope");
    scope.add(p.name);
    return {name:p.name,scope:p.scope,upper:p.upper};
  });
  // Type parameters are in scope throughout their parameter list. The current
  // source slice emits only earlier-parameter bounds, but the wire does not
  // bake that implementation restriction into the eventual full language.
  const parameters: DirectParameter[] = rawParameters.map((p) => ({
    name:p.name, scope:p.scope,
    upper:p.upper === null ? null : directType(p.upper,size,scope),
  }));
  const context: DirectBinding[] = j.context.map((raw) => {
    const b = record(raw,["name","type"]);
    if (typeof b.name !== "string") throw Error("invalid direct-obligation binding");
    return {name:b.name,type:directType(b.type,size,scope)};
  });
  const actual = directType(j.actual,size,scope), expected = directType(j.expected,size,scope);
  if (j.kind === "subtyping") {
    if (j.body !== undefined) throw Error("invalid subtyping judgment fields");
    return {kind:"subtyping",parameters,context,subject:directSubject(j.subject),actual,expected};
  }
  if (j.kind === "scheme-introduction") {
    if (j.subject !== undefined) throw Error("invalid scheme judgment fields");
    const body = directSubject(j.body);
    if (body.kind !== "closure-body") throw Error("scheme introduction needs a closure body");
    return {kind:"scheme-introduction",parameters,context,body,actual,expected};
  }
  throw Error("unknown direct-obligation judgment");
}
function knowledge(v: unknown) {
  if (v === null) return;
  const k = record(v,["cells","values","links"]);
  for (const key of ["cells","values"]) {
    if (!Array.isArray(k[key])) throw Error("invalid heap facts");
    for (const fact of k[key]) {
      const f = record(fact,["slot","contents","field"]); nat(f.slot);
      if (typeof f.field !== "string") throw Error("invalid heap fact field");
      if (!Array.isArray(f.contents)) throw Error("invalid heap contents");
      f.contents.forEach(heapAtom);
    }
  }
  if (!Array.isArray(k.links)) throw Error("invalid heap links");
  for (const link of k.links) {
    const l = record(link,["cell","value","alias","field","distinct","other"]); nat(l.cell); nat(l.value);
    if (typeof l.distinct !== "boolean") throw Error("invalid distinct flag");
    if (typeof l.other !== "string") throw Error("invalid link field");
    if (typeof l.field !== "string") throw Error("invalid heap link field");
    if (typeof l.alias !== "boolean") throw Error("invalid alias");
  }
}
function diagnosticNode(v: unknown, size: number) {
  const n = record(v,["label","sourceMap","node","claim","requiredKnowledge"]);
  nat(n.label); sourceMap(n.sourceMap); knowledge(n.requiredKnowledge);
  if (n.claim !== null) {
    const c = record(n.claim,["context","type"]);
    if (!Array.isArray(c.context)) throw Error("invalid context");
    c.context.forEach(t => decodeLabels(t,size)); decodeLabels(c.type,size);
  }
  if (n.node !== null) {
    const node = record(n.node,["expression","continuation"]); decodeTerm(node.expression);
  }
}

export function readDiagnostic(
  detail: string,
): ObligationDiagnostic | undefined {
  const lines = detail.split(/\r?\n/).filter((line) => line.startsWith(PREFIX));
  if (lines.length !== 1) return undefined;
  let d: Record<string, unknown>;
  try {
    const parsed: unknown = JSON.parse(lines[0].slice(PREFIX.length));
    if (!isRecord(parsed)) return undefined;
    d = parsed;
    const variants: Record<string,string[]> = {
      "node-typing":["id","source","sequent"], "expression-claim":["id","sourceMap","sequent"],
      "direct-obligation":["id","sourceMap","judgment"],
      "source-refusal":["id","sourceMap","reason"],
      "edge-coverage":["id","edgeIndex","source","destination","transfer"], "production-failure":["failure"],
    };
    if (typeof d.kind !== "string" || !variants[d.kind]) return undefined;
    record(d,["phase","outcome","fuel","types","kind",...variants[d.kind]],["requiredResult"]);
    // The graph decides how many labels there are, so it is decoded first and
    // everything after counts against what it returned.
    const types = decodeGraph(d.types);
    if (d.source !== undefined) diagnosticNode(d.source,types.length);
    if (d.destination !== undefined) diagnosticNode(d.destination,types.length);
    if (d.sourceMap !== undefined) sourceMap(d.sourceMap);
    if (d.kind === "direct-obligation") {
      const judgment = directJudgment(d.judgment,types.length);
      const at = judgment.kind === "subtyping" ? judgment.subject.pos : judgment.body.pos;
      const map = d.sourceMap;
      if (map === null || map === undefined) return undefined;
      if (map.pos[0] !== at[0] || map.pos[1] !== at[1] ||
          map.context.map((x) => x.name).join("\0") !== judgment.context.map((x) => x.name).join("\0"))
        return undefined;
      d.judgment = judgment;
    }
    if (d.kind === "source-refusal" && typeof d.reason !== "string") return undefined;
    if (d.kind === "production-failure" && typeof d.failure !== "string") return undefined;
    const labels = (v: unknown) => decodeLabels(v,types.length);
    if (d.requiredResult !== undefined) labels(d.requiredResult);
    if (d.kind === "node-typing" || d.kind === "expression-claim") {
      const q = d.sequent;
      if (!isRecord(q) || Object.keys(q).sort().join() !== "context,term,type" || !Array.isArray(q.context)) return undefined;
      q.context.forEach(labels); labels(q.type); decodeTerm(q.term);
    }
    if (d.kind === "edge-coverage") {
      nat(d.edgeIndex);
      const transfer = record(d.transfer,["available","target","booleanObservation","tagObservation"]);
      const target = record(transfer.target,["label","mapping"]);
      if (transfer.tagObservation !== null) {
        const tag = record(transfer.tagObservation,["test","answer","slot"]);
        nat(tag.slot);
        if (!isTag(tag.test) || typeof tag.answer !== "boolean") return undefined;
      }
      const destination = record(d.destination,["label","sourceMap","node","claim","requiredKnowledge"]);
      const claim = destination.claim;
      const available = transfer.available;
      if (!isRecord(claim) || !Array.isArray(available) || !Array.isArray(claim.context)) return undefined;
      available.forEach(labels); claim.context.forEach(labels);
      if (!Number.isSafeInteger(target.label)) return undefined;
      const mapping = target.mapping;
      if (mapping !== null && (!Array.isArray(mapping) || mapping.some(i => typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= available.length))) return undefined;
      if (transfer.booleanObservation !== null && typeof transfer.booleanObservation !== "boolean") return undefined;
    }
  } catch {
    return undefined;
  }
  if (
    !PHASES.includes(d.phase) ||
    d.outcome !== "not-established" ||
    !Array.isArray(d.types) ||
    typeof d.fuel !== "number" ||
    !Number.isSafeInteger(d.fuel) ||
    d.fuel < 0
  )
    return undefined;
  if (!KINDS.includes(d.kind)) return undefined;
  if (d.kind !== "production-failure" && typeof d.id !== "string")
    return undefined;
  if (d.kind === "edge-coverage" && (!d.source || !d.destination || !d.transfer))
    return undefined;
  if (
    (d.kind === "node-typing" || d.kind === "expression-claim") &&
    !d.sequent
  )
    return undefined;
  // Checked field by field above, variant by variant: this is where that
  // becomes a type, and the only assertion this file makes.
  return d as unknown as ObligationDiagnostic;
}
