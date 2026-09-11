/*
 * The `stateful-source-v3` wire format, described once.
 *
 * A producer states, for one source file, what it believes at every site the
 * lowering visits; the verifier asks whether those beliefs are derivable.
 * SOURCE-CLAIMS.md specifies the format in prose; this is the same thing for
 * the tools that write and read it, so the producer and the consumer cannot
 * drift apart silently.
 */

/** A half-open span of the original source, in UTF-16 code units. */
export type Span = [start: number, end: number];

/**
 * A type, as a sorted list of row indices into the document's own table. The
 * list is a union: `[1, 2]` is `true | false`, and the empty list is `never`.
 */
export type Labels = number[];

/**
 * One row of the document's type table. The first four rows are fixed — null,
 * true, false, undefined — and every other row is a clause the file mentions,
 * interned on first use. The clause encoding is the verifier's own, decoded in
 * Lean rather than here, so it stays opaque at this boundary.
 */
export type Row = unknown[];

/**
 * What a producer believes at one site: the type it claims, and — where the
 * site is a cell read and the producer tracks cell contents — what the cell
 * holds at that point. `current` is required and explicitly `null` where no
 * such assertion is made, so silence is stated rather than inferred.
 */
export interface Point {
  type: Labels;
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
  result: Labels;
  entries: EntryClaim[];
  expressions: ExpressionClaim[];
}

export interface SourceClaims {
  version: 3;
  profile: "stateful-source-v3";
  file: string;
  sourceSha256: string;
  types: Row[];
  functions: FunctionClaims[];
}
