/*
 * The producer-independent source sidecar, described once.
 *
 * A producer states, for one source file, what it believes at every site the
 * lowering visits; the verifier asks whether those beliefs are derivable.
 * SOURCE-CLAIMS.md specifies the format in prose; this is the same thing for
 * the tools that write and read it, so the producer and the consumer cannot
 * drift apart silently. A document either has exactly this shape, which every
 * decoder requires field by field, or it is rejected.
 */

import type { Span } from "./span.mts";
import type { Labels, Row } from "./type-graph.mts";
export type { Labels, Row } from "./type-graph.mts";

/** Ground graph labels or a reference to the enclosing function's source binder. */
export type ClaimType = Labels | { param: string } | { unavailable: string };

/**
 * What a producer believes at one site: the type it claims, and — where the
 * site is a cell read and the producer tracks cell contents — what the cell
 * holds at that point. `current` is required and explicitly `null` where no
 * such assertion is made, so silence is stated rather than inferred.
 */
export interface Point {
  type: ClaimType;
  current: Labels | null;
}

/** A named point: a parameter, or a binding visible at a statement entry. */
export interface NamedPoint extends Point {
  name: string;
}

/** The environment at one statement entry, keyed by the statement's start. */
export interface EntryClaim {
  start: number;
  bindings: NamedPoint[];
}

export interface ExpressionClaim extends Point {
  pos: Span;
}

export interface FunctionClaims {
  name: string;
  namePos: Span;
  params: NamedPoint[];
  result: ClaimType;
  entries: EntryClaim[];
  expressions: ExpressionClaim[];
}

export interface SourceClaims {
  file: string;
  sourceSha256: string;
  types: Row[];
  functions: FunctionClaims[];
}
