/*
 * SKJS's own claims export: what its checker believes at each site of one file.
 *
 * SKJS writes this document (`skjs.sh --emit-skjs-type-claims`); everything
 * here only ever reads it, or edits a copy of it. The producer is outside this
 * repository, so this declaration is what the repository reads of the document
 * rather than the document's own definition: a field SKJS adds is ignored, and
 * a field it renames is a compile error at every reader at once instead of
 * `undefined` at one use site. `Fragment.lean`'s `decodeClaims` reads the same
 * document on the Lean side, and is what actually checks a document's shape.
 *
 * A claimed type is whatever the producer encoded — the structural claim
 * language of claim.mts, or a marker saying the producer could not decode one.
 * It is `unknown` here because this document does not say which.
 */

import type { Span } from "./span.mts";
import type { ClosedOperation } from "./skjs-operations.mts";

/** How complete the producer's own collection was, as the document carries it.
 * `Collection` in report-viewer/types.ts names the same fields once a report
 * has been read back and checked; a document arriving here has not been. */
export interface SkjsCollection {
  completion: string;
  quality: string;
  mode: string;
  /** Original spans expression checking entered (../ANNOTATED-SOURCE.md). */
  visitedExpressions?: number[][];
}

/** A parameter, or a binding of a statement entry's environment. */
export interface SkjsNamedPoint {
  name: string;
  type: unknown;
  /** Whether the binding can be assigned to, where the producer says. */
  mutable?: boolean;
  /** The type the source declares, where that differs from the narrowed one. */
  declared?: unknown;
}

/** The environment at one statement entry. The whole statement's span is
 * carried, though only its start addresses the entry. */
export interface SkjsEntry {
  pos: Span;
  vars: SkjsNamedPoint[];
}

export interface SkjsExpression {
  pos: Span;
  type: unknown;
}

export interface SkjsFunction {
  name: string;
  namePos: Span;
  params: SkjsNamedPoint[];
  retType: unknown;
  envs: SkjsEntry[];
  exprs: SkjsExpression[];
  /** The sites written to, which the producer states separately from the
   * expressions it read. */
  lvalues?: SkjsExpression[];
  /** Absent where the producer said nothing about its own collection. */
  collection?: SkjsCollection;
  /** Advisory, and validated before use: shape unknown until then. */
  unavailableTypes?: unknown[];
  /** The closed judgments SKJS recorded while checking this function, which
   * skjs-operations.mts owns and `--check-skjs-operations` verifies. */
  operations?: ClosedOperation[];
}

export interface SkjsFile {
  file: string;
  functions: SkjsFunction[];
}

/** One document: an entry per file the producer was asked about. */
export type SkjsClaims = SkjsFile[];

/** The entry for one file. Every reader here wants exactly one, so a document
 * that says nothing about the file is the caller asking for the wrong thing. */
export function fileOf(claims: SkjsClaims, file: string): SkjsFile {
  const found = claims.find((f) => f.file === file);
  if (!found) throw Error(`the producer said nothing about ${file}`);
  return found;
}

/** One function of one file, by name. Names repeat across files, never within
 * one: the producer states each declaration once. */
export function functionOf(claims: SkjsClaims, file: string, name: string): SkjsFunction {
  const found = fileOf(claims, file).functions.find((f) => f.name === name);
  if (!found) throw Error(`the producer said nothing about ${name} in ${file}`);
  return found;
}
