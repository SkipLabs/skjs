/** The closed subtype and expansion judgments SKJS records in its
 * `--emit-skjs-type-claims` export. Tools that read these judgments are typed
 * against this shape; an added or removed field is a compile error at those
 * sites. This is SKJS's own encoding, not the independent sidecar. */
import { decodeClaimType, type ClaimType } from "./claim.mts";

export type OperationKind = "subtype" | "expand";

/** A closed subtype or expansion judgment, serialized at the snapshot in force. */
export interface ClosedOperation {
  kind: OperationKind;
  source: ClaimType;
  target: ClaimType;
}

const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
export function decodeClosedOperation(v: unknown): ClosedOperation {
  if (!isRecord(v)) throw Error("expected an operation object");
  const o = v;
  if (Object.keys(o).some(k => !["kind", "source", "target"].includes(k)) ||
      !("kind" in o && "source" in o && "target" in o))
    throw Error("unexpected or missing operation field");
  if (o.kind !== "subtype" && o.kind !== "expand") throw Error("unknown operation kind");
  return { kind: o.kind, source: decodeClaimType(o.source), target: decodeClaimType(o.target) };
}
