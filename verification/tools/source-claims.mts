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

/** A quantified callable. Parameter references inside it are resolved
 * lexically: its binders shadow enclosing binders only within this value. */
export interface SchemeClaim {
  typeParams: { name: string; bound: ClaimType | null }[];
  /** The receiver a call passes; an unknown row when any is accepted. */
  this: ClaimType;
  params: ClaimType[];
  rest: ClaimType | null;
  result: ClaimType;
}

/** Ground graph labels, a lexically scoped rigid parameter, their union, or a quantified
 * callable. This is the one type language shared by every producer. */
export type ClaimType =
  | Labels
  | { param: string }
  | { array: ClaimType }
  | { union: ClaimType[] }
  | { scheme: SchemeClaim }
  | { unavailable: string };

/**
 * What a producer believes at one site: the type it claims, and — where the
 * site names a record and the producer tracks its contents — what each named
 * field holds at that point. An object has one location per field, so the
 * assertion names the field it is about. `current` is required and explicitly
 * `null` where no such assertion is made, so silence is stated rather than
 * inferred.
 */
export type CurrentFields = [name: string, labels: Labels][];

export interface Point {
  type: ClaimType;
  current: CurrentFields | null;
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

/** The type arguments one call supplies for a scheme's binders. It records the
 * elimination a producer proposes; the verifier re-checks it against the
 * scheme's signature and never infers one of its own. Absent at every site that
 * is not a call to a quantified callable. */
export interface TypeArgument {
  name: string;
  type: ClaimType;
}

export interface ExpressionClaim extends Point {
  pos: Span;
  instantiate?: TypeArgument[] | null;
}

export interface FunctionClaims {
  name: string;
  namePos: Span;
  params: NamedPoint[];
  result: ClaimType;
  entries: EntryClaim[];
  expressions: ExpressionClaim[];
  /** One interior claim set per advertised signature of the closure at pos. */
  arrows?: {
    pos: Span;
    rows: { expressions: ExpressionClaim[]; entries: EntryClaim[] }[];
  }[];
}

export interface SourceClaims {
  file: string;
  sourceSha256: string;
  types: Row[];
  functions: FunctionClaims[];
  /** The module initialization unit, present exactly when the source has
   * top-level code: its entries and expressions, with no parameters. */
  init?: Pick<FunctionClaims, "entries" | "expressions" | "arrows">;
  /** Generic applications the producer reserved empty rows for, which Lean
   * fills from the declarations: row, declaration position, argument rows. */
  applications?: { row: number; declaration: number; args: number[][] }[];
}
