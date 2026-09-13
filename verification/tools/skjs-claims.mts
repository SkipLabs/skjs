/** SKJS `--emit-skjs-type-claims` export. Tools that read this document are
 * typed against this shape; an added or removed field is a compile error at
 * those sites. This is SKJS's own encoding, not the independent sidecar. */
import { decodeClaimType, type WireType } from "./claim-language.mts";

export type Span = [start: number, end: number];

export type OperationKind = "subtype" | "expand";

/** A closed subtype or expansion judgment, serialized at the snapshot in force. */
export interface ClosedOperation {
  kind: OperationKind;
  source: WireType;
  target: WireType;
}

export function decodeClosedOperation(v: unknown): ClosedOperation {
  if (!v || typeof v !== "object" || Array.isArray(v)) throw Error("expected an operation object");
  const o = v as Record<string, unknown>;
  if (Object.keys(o).some(k => !["kind", "source", "target"].includes(k)) ||
      !("kind" in o && "source" in o && "target" in o))
    throw Error("unexpected or missing operation field");
  if (o.kind !== "subtype" && o.kind !== "expand") throw Error("unknown operation kind");
  return { kind: o.kind, source: decodeClaimType(o.source), target: decodeClaimType(o.target) };
}
