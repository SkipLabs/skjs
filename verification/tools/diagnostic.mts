import { decodeGraph, decodeLabels, type TypeGraph, type Labels } from "./type-graph.mts";
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
export interface HeapFact {
  slot: number;
  contents: ("nul" | "undef" | "tru" | "fls")[];
  field: string;
}
export interface HeapKnowledge {
  cells: HeapFact[]; values: HeapFact[];
  links: {cell: number; value: number; alias: boolean; field: string}[];
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

const PHASES: readonly unknown[] = [
  "proof-search",
  "certificate-check",
  "request-validation",
];
const KINDS: readonly unknown[] = [
  "node-typing",
  "edge-coverage",
  "expression-claim",
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
      const f = record(fact,["slot","contents","field"]); nat(f.slot);
      if (typeof f.field !== "string") throw Error("invalid heap fact field");
      if (!Array.isArray(f.contents) || f.contents.some(x => !["nul","undef","tru","fls"].includes(x))) throw Error("invalid heap contents");
    }
  }
  if (!Array.isArray(k.links)) throw Error("invalid heap links");
  for (const link of k.links) {
    const l = record(link,["cell","value","alias","field"]); nat(l.cell); nat(l.value);
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
