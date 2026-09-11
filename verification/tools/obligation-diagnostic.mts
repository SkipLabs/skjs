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

export interface ObligationDiagnostic {
  version: 2;
  phase: Phase;
  outcome: "not-established";
  kind: Kind;
  /** The proof budget the search was given. */
  fuel: number;
  types: unknown[];
  /** The node or expression the record is about; absent for a production failure. */
  id?: string;
  source?: unknown;
  destination?: unknown;
  transfer?: unknown;
  sequent?: unknown;
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
