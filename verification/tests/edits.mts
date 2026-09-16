/*
 * Reaching into a program and its claims, for the suites that alter them.
 *
 * A suite here changes one thing about a document and requires the verifier to
 * reject the result. The alteration is written against the declared languages
 * — the fragment tree of tools/fragment.mts, the producer's claims of
 * tools/skjs-claims.mts — so a suite names the construct it is reaching into
 * and a fixture that stops having that shape fails at the line that names it,
 * rather than as something unrelated further on. What the alteration then
 * writes is deliberately outside those languages; that is the point of it, and
 * the claim fields it writes are `unknown` for exactly that reason.
 */
import type { Ast, Expr, FunctionAst, Stmt } from "../tools/fragment.mts";
import type { Span } from "../tools/span.mts";
import { decodeClaimType, type Atom, type ClaimType } from "../tools/claim.mts";
import type {
  SkjsClaims,
  SkjsEntry,
  SkjsExpression,
  SkjsFunction,
  SkjsNamedPoint,
} from "../tools/skjs-claims.mts";

const found = <T,>(what: string, value: T | undefined): T => {
  if (value === undefined) throw Error(`this fixture has no ${what}`);
  return value;
};

/** The members of a tagged union one tag selects. `Extract` will not do: some
 * members carry several tags, and are the same node whichever it is. */
type OfKind<T extends { k: string }, K extends T["k"]> = T extends unknown
  ? K extends T["k"]
    ? T
    : never
  : never;
type OfTag<T extends { a: string }, K extends T["a"]> = T extends unknown
  ? K extends T["a"]
    ? T
    : never
  : never;

/** Whether a node carries the tag named, which is what selects its members. */
const isKind = <T extends { k: string }, K extends T["k"]>(
  node: T,
  k: K,
): node is OfKind<T, K> => node.k === k;
const isTagged = <T extends { a: string }, K extends T["a"]>(
  node: T,
  a: K,
): node is OfTag<T, K> => node.a === a;

/** The statement at a place in a body, as the kind the suite names. */
export function stmt<K extends Stmt["k"]>(
  s: Stmt | undefined,
  k: K,
): OfKind<Stmt, K> {
  if (s === undefined || !isKind(s, k))
    throw Error(`expected a ${k} statement, found ${s?.k ?? "none"}`);
  return s;
}

/** The expression at a place in a tree, as the kind the suite names. */
export function expr<K extends Expr["k"]>(
  e: Expr | undefined,
  k: K,
): OfKind<Expr, K> {
  if (e === undefined || !isKind(e, k))
    throw Error(`expected a ${k} expression, found ${e?.k ?? "none"}`);
  return e;
}

/** One function of a parse, by name. */
export const fn = (ast: Ast, name: string): FunctionAst =>
  found(`function ${name}`, ast.functions.find((f) => f.name === name));

/** The statement at an index of a body, and the one it ends with. */
export const at = (body: Stmt[], i: number): Stmt =>
  found(`statement ${i}`, body[i]);
export const last = (body: Stmt[]): Stmt =>
  found("statement to end with", body[body.length - 1]);

/* ---------- the claims beside it ---------- */

/** The one function a single-function fixture states claims for. */
export const only = (claims: SkjsClaims, file: string): SkjsFunction =>
  found(`claims for ${file}`, claims.find((f) => f.file === file)?.functions[0]);

/** The claim stated for an expression's whole span. A call and its callee
 * begin together, so the end is what tells two claims there apart. */
export const claimAt = (f: SkjsFunction, pos: Span): SkjsExpression =>
  found(`claim at ${pos.join(":")}`,
    f.exprs.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]));

/** The claim stated at an expression's own start, where a suite addresses it
 * by that alone. */
export const claimFrom = (f: SkjsFunction, start: number): SkjsExpression =>
  found(`claim at ${start}`, f.exprs.find((e) => e.pos[0] === start));

/** The environment stated at a statement entry. */
export const entryAt = (f: SkjsFunction, start: number): SkjsEntry =>
  found(`entry at ${start}`, f.envs.find((e) => e.pos[0] === start));

/** One binding of that environment. */
export const binding = (
  f: SkjsFunction,
  start: number,
  name: string,
): SkjsNamedPoint =>
  found(`claim for ${name} at ${start}`,
    entryAt(f, start).vars.find((v) => v.name === name));

/** What a producer stated at a site, decoded: an alteration changes it as the
 * claim language of claim.mts, and changes it where it is, so the rest of the
 * claim stays exactly as the producer wrote it. A claim that does not decode
 * is this fixture having changed, not something to alter. */
export const claimType = (claim: { type: unknown }): ClaimType =>
  decodeClaimType(claim.type);

/** One atom of a claim, as the kind the suite names. */
export function atom<K extends Atom["a"]>(a: Atom | undefined, k: K): OfTag<Atom, K> {
  if (a === undefined || !isTagged(a, k))
    throw Error(`expected a ${k} atom, found ${a?.a ?? "none"}`);
  return a;
}

/* ---------- documents this repository states no type for ---------- */
/* Evidence and requests have no TypeScript mirror: the verifier is their only
 * reader, so there is no second one to keep in step. A suite that alters one
 * says what it expects to find, step by step, and fails where it says it. */

const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);

/** One value inside such a document, by the path that reaches it. */
export function field(value: unknown, ...path: (string | number)[]): unknown {
  let at = value;
  for (const [i, key] of path.entries()) {
    const so_far = path.slice(0, i + 1).join(".");
    if (typeof key === "number") {
      if (!Array.isArray(at)) throw Error(`${so_far} is not a list`);
      at = at[key];
    } else {
      if (!isRecord(at)) throw Error(`${so_far} is not a record`);
      at = at[key];
    }
  }
  return at;
}

/** That value, as the record or the list a suite reaches into. */
export function record(value: unknown, what: string): Record<string, unknown> {
  if (!isRecord(value)) throw Error(`${what} is not a record`);
  return value;
}
export function list(value: unknown, what: string): unknown[] {
  if (!Array.isArray(value)) throw Error(`${what} is not a list`);
  return value;
}
