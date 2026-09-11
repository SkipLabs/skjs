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

export interface ObligationDiagnostic {
  version: 2;
  phase: Phase;
  outcome: "not-established";
  kind: Kind;
  /** The proof budget the search was given. */
  fuel: number;
  types: unknown[];
  requiredResult?: unknown;
  /** The node or edge the record is about; absent for a production failure. */
  id?: string;
  /** Present for every kind but a production failure. */
  source?: DiagnosticNode;
  /** Edge coverage only. */
  destination?: DiagnosticNode;
  edgeIndex?: number;
  transfer?: DiagnosticTransfer | null;
  /**
   * A closure expression claim names its place directly: that failure is
   * raised where the claim is, not at a node of the certificate graph, so it
   * carries the entry itself rather than a `source` node holding one
   * (ExpressionClaims.lean, against `failureDiagnostic` in RequestJson.lean).
   */
  sourceMap?: SourceMapEntry;
  /** Node typing and expression claims only. */
  sequent?: { context: unknown[]; expression?: unknown; type?: unknown } | null;
  /** Production failure only. */
  failure?: string;
  /** Attached by the report writer, not by the verifier. */
  input?: {
    file: string;
    functionName: string;
    namePos: [number, number];
    sourceSha256: string;
    claimsSha256: string;
  };
}

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
