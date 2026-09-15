import { decodeGraph, decodeLabels, type TypeGraph, type Labels } from "./type-graph.mts";
import { decodeTerm, type Term } from "./calculus.mts";
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

export interface HeapFact { slot: number; contents: ("nul" | "undef" | "tru" | "fls")[] }
export interface HeapKnowledge {
  cells: HeapFact[]; values: HeapFact[];
  links: {cell: number; value: number; alias: boolean}[];
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
  tagObservation: { test: unknown; answer: boolean; slot: number } | null;
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
  sequent: Sequent | null;
}

/** An edge's destination was not justified by what its source carries. */
export interface EdgeCoverage extends Common {
  kind: "edge-coverage";
  id: string;
  edgeIndex: number;
  source: DiagnosticNode;
  destination: DiagnosticNode;
  transfer: DiagnosticTransfer | null;
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
  sequent: Sequent | null;
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
  | ProductionFailure;

const PHASES: readonly string[] = [
  "proof-search",
  "certificate-check",
  "request-validation",
];
const KINDS: readonly string[] = [
  "node-typing",
  "edge-coverage",
  "expression-claim",
  "production-failure",
];
const PREFIX = "obligation-diagnostic: ";

function record(v: unknown, required: string[], optional: string[] = []): Record<string, unknown> {
  if (!v || typeof v !== "object" || Array.isArray(v) || required.some(k => !(k in v)) || Object.keys(v).some(k => ![...required,...optional].includes(k))) throw Error("invalid diagnostic fields");
  return v as Record<string, unknown>;
}
function nat(v: unknown) { if (!Number.isSafeInteger(v) || (v as number) < 0) throw Error("invalid diagnostic index"); }
function span(v: unknown) { if (!Array.isArray(v) || v.length !== 2) throw Error("invalid diagnostic span"); v.forEach(nat); if (v[1] < v[0]) throw Error("reversed span"); }
function sourceMap(v: unknown) {
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
function knowledge(v: unknown) {
  if (v === null) return;
  const k = record(v,["cells","values","links"]);
  for (const key of ["cells","values"]) {
    if (!Array.isArray(k[key])) throw Error("invalid heap facts");
    for (const fact of k[key]) {
      const f = record(fact,["slot","contents"]); nat(f.slot);
      if (!Array.isArray(f.contents) || f.contents.some(x => !["nul","undef","tru","fls"].includes(x))) throw Error("invalid heap contents");
    }
  }
  if (!Array.isArray(k.links)) throw Error("invalid heap links");
  for (const link of k.links) {
    const l = record(link,["cell","value","alias"]); nat(l.cell); nat(l.value);
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
    const parsed: unknown = JSON.parse(lines[0]!.slice(PREFIX.length));
    if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) return undefined;
    d = parsed as Record<string, unknown>;
    const variants: Record<string,string[]> = {
      "node-typing":["id","source","sequent"], "expression-claim":["id","sourceMap","sequent"],
      "edge-coverage":["id","edgeIndex","source","destination","transfer"], "production-failure":["failure"],
    };
    if (typeof d.kind !== "string" || !variants[d.kind]) return undefined;
    record(d,["phase","outcome","fuel","types","kind",...variants[d.kind]],["requiredResult"]);
    decodeGraph(d.types);
    if (d.source !== undefined) diagnosticNode(d.source,(d.types as TypeGraph).length);
    if (d.destination !== undefined) diagnosticNode(d.destination,(d.types as TypeGraph).length);
    if (d.sourceMap !== undefined) sourceMap(d.sourceMap);
    if (d.kind === "production-failure" && typeof d.failure !== "string") return undefined;
    const labels = (v: unknown) => decodeLabels(v,(d.types as TypeGraph).length);
    if (d.requiredResult !== undefined) labels(d.requiredResult);
    if (d.kind === "node-typing" || d.kind === "expression-claim") {
      const q = d.sequent as Sequent;
      if (!q || Object.keys(q).sort().join() !== "context,term,type" || !Array.isArray(q.context)) return undefined;
      q.context.forEach(labels); labels(q.type); decodeTerm(q.term);
    }
    if (d.kind === "edge-coverage") {
      nat(d.edgeIndex);
      record(d.transfer,["available","target","booleanObservation","tagObservation"]);
      const transfer = d.transfer as DiagnosticTransfer;
      record(transfer.target,["label","mapping"]);
      if (transfer.tagObservation !== null) {
        const tag = record(transfer.tagObservation,["test","answer","slot"]);
        nat(tag.slot);
        if (!["isNul","isBool","isRef","isFun","isUndef","isNullish"].includes(tag.test as string) || typeof tag.answer !== "boolean") return undefined;
      }
      const destination = d.destination as DiagnosticNode;
      if (!transfer || !destination?.claim || !Array.isArray(transfer.available) || !Array.isArray(destination.claim.context)) return undefined;
      transfer.available.forEach(labels); destination.claim.context.forEach(labels);
      if (!transfer.target || !Number.isSafeInteger(transfer.target.label)) return undefined;
      const mapping = transfer.target.mapping;
      if (mapping !== null && (!Array.isArray(mapping) || mapping.some(i => !Number.isSafeInteger(i) || i < 0 || i >= transfer.available.length))) return undefined;
      if (transfer.booleanObservation !== null && typeof transfer.booleanObservation !== "boolean") return undefined;
    }
  } catch {
    return undefined;
  }
  if (
    !PHASES.includes(d.phase as string) ||
    d.outcome !== "not-established" ||
    !Array.isArray(d.types) ||
    !Number.isSafeInteger(d.fuel) ||
    (d.fuel as number) < 0
  )
    return undefined;
  if (!KINDS.includes(d.kind as string)) return undefined;
  if (d.kind !== "production-failure" && typeof d.id !== "string")
    return undefined;
  if (d.kind === "edge-coverage" && (!d.source || !d.destination || !d.transfer))
    return undefined;
  if (
    (d.kind === "node-typing" || d.kind === "expression-claim") &&
    !d.sequent
  )
    return undefined;
  return d as unknown as ObligationDiagnostic;
}
