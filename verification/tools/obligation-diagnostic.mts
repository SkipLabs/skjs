// Optional explanatory metadata, never evidence. Unknown versions are left in
// the human diagnostic; they must not change the verification outcome.

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
  pos: [number, number];
  role: string;
  environmentStart: number | null;
  context: unknown[];
}

/** The judgement a failure could not establish. */
export interface Sequent {
  context: unknown[];
  expression?: unknown;
  type?: unknown;
}

/** A node of the certificate graph, as the failure reports it. */
export interface DiagnosticNode {
  label: number;
  sourceMap: SourceMapEntry | null;
  node: unknown;
  claim: { context: unknown[]; type?: unknown } | null;
  requiredKnowledge: { cells?: { contents?: unknown }[] } | null;
}

/**
 * What an edge carries from its source to its destination, mirroring the
 * continuation the source node ends in (RequestJson.lean, `failureDiagnostic`).
 */
export interface DiagnosticTransfer {
  available: unknown[];
  target: { label: number; mapping: number[] };
  /** Which way a two-armed Boolean test went; null for every other edge. */
  booleanObservation: boolean | null;
  /** The tag test an edge answers, where the continuation is one. */
  tagObservation: { test: unknown; answer: boolean; slot: number } | null;
}

/** What every record carries, whatever the failure was. */
interface Common {
  version: 2;
  phase: Phase;
  outcome: "not-established";
  /** The proof budget the search was given. */
  fuel: number;
  types: unknown[];
  /**
   * The result type the request asked for. Absent from a closure expression
   * claim, which is produced without a request and so has none — not an
   * omission to paper over.
   */
  requiredResult?: unknown;
  /** Attached by the report writer, not by the verifier. */
  input?: {
    file: string;
    functionName: string;
    namePos: [number, number];
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

export function readDiagnostic(
  detail: string,
): ObligationDiagnostic | undefined {
  const lines = detail.split(/\r?\n/).filter((line) => line.startsWith(PREFIX));
  if (lines.length !== 1) return undefined;
  let d: Record<string, unknown>;
  try {
    d = JSON.parse(lines[0]!.slice(PREFIX.length));
  } catch {
    return undefined;
  }
  if (
    d?.version !== 2 ||
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
