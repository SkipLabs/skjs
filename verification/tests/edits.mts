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
import type { Ast, BindingAst, Expr, FunctionAst, Stmt } from "../tools/fragment.mts";
import type { Span } from "../tools/span.mts";
import { decodeClaimType, type Atom, type ClaimType } from "../tools/claim.mts";
import type { TypeTerm } from "../tools/declaration-types.mts";
import type {
  SkjsClaims,
  SkjsEntry,
  SkjsExpression,
  SkjsFunction,
  SkjsNamedPoint,
} from "../tools/skjs-claims.mts";

/** A value the suite requires the fixture to have. */
export const must = <T,>(value: T | null | undefined, what: string): T => {
  if (value === null || value === undefined)
    throw Error(`this fixture has no ${what}`);
  return value;
};
const found = <T,>(what: string, value: T | undefined): T => must(value, what);

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

/** The one binding of a declaration that declares one, which is how the
 * suites here address a `const` or `let`. A list is reached by index instead. */
export function sole(s: OfKind<Stmt, "const" | "let">): BindingAst {
  if (s.bindings.length !== 1)
    throw Error(`expected one binding, found ${s.bindings.length}`);
  return s.bindings[0];
}

/** The initializer of an allocation's single field, for a fixture that
 * allocates one. A record with several fields is reached by index instead. */
export const allocField = (e: Expr | undefined): Expr =>
  must(expr(e, "alloc").fields[0], "an allocated field").e;

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

/** A node as the plain record it is, for a check that writes a field neither
 * language has — which is what that check is about: the reader must refuse it.
 * Everything else is written as the language it belongs to. */
export const written = (node: object): Record<string, unknown> =>
  record(node, "a node");

/** A table of alterations written inline, given the row type it is written as.
 * An annotation the compiler checks against every row, where the cast this
 * replaces would have been believed instead. */
export const rows = <T,>(table: T[]): T[] => table;

/** The source term an annotation writes for a claim-shaped type: the fragment
 * tree states annotations as terms, and a suite that alters one says what it
 * means in the claim language it checks against. Spans are empty; nothing
 * reads them. */
export function sourceType(type: ClaimType): TypeTerm {
  const span: Span = [0, 0];
  const of = (a: Atom): TypeTerm => {
    const and = "and" in a && a.and?.length ? a.and : null;
    if (and) return { k: "intersection", parts: [of({ ...a, and: [] } as Atom), ...and.map(of)], span };
    switch (a.a) {
      case "null": case "undefined": case "boolean": case "number": case "string": case "void":
        return { k: "atom", name: a.a, span };
      case "booleanlit":
        return { k: "literal", name: a.v === "true" ? "true" : "false", text: a.v, span };
      case "numberlit": case "stringlit":
        return { k: "literal", name: a.a === "numberlit" ? "number" : "string", text: a.v, span };
      case "param": return { k: "binder", name: a.name, span };
      case "array":
        return !a.required.length && !a.optional.length && a.rest
          ? { k: "array", readonly: a.readonly, element: sourceType(a.rest), span }
          : { k: "tuple", readonly: a.readonly, required: a.required.map(sourceType),
              optional: a.optional.map(sourceType), rest: a.rest ? sourceType(a.rest) : null, span };
      case "function":
        return { k: "function", receiver: a.this.top ? null : sourceType(a.this),
          params: a.params.map(sourceType), rest: a.rest ? sourceType(a.rest) : null,
          result: sourceType(a.result), span };
      case "record":
        return { k: "object", fields: a.fields.map(f => ({ name: f.name, optional: f.optional,
          readonly: !f.write.top && !f.write.atoms.length && (f.read.top || f.read.atoms.length > 0),
          type: sourceType(f.read), span })),
          stringIndex: a.indexSignature ? { readonly: true, value: sourceType(a.indexSignature.read), span } : null,
          calls: [], span };
      default: throw Error(`no source term for a ${a.a} atom`);
    }
  };
  if (type.top) return { k: "atom", name: "unknown", span };
  const parts = type.atoms.map(of);
  if (!parts.length) return { k: "atom", name: "never", span };
  return parts.length === 1 && parts[0] ? parts[0] : { k: "union", parts, span };
}

/** The source term of one kind the fixture's annotation must be. */
export function term<K extends TypeTerm["k"]>(t: TypeTerm | null | undefined, k: K): OfKind<TypeTerm, K> {
  if (!t || t.k !== k) throw Error(`this fixture has no ${k} term`);
  return t as OfKind<TypeTerm, K>;
}
