#!/usr/bin/env node
/*
 * A second claims producer for `stateful-source-v3`. Where SKJS's own export
 * (`skjs.sh --emit-skjs-type-claims`) states what SKJS's checker believes at
 * every site of a source fragment file, this states what the TypeScript
 * compiler's own checker believes at the same sites, so the two can be run
 * through the same independent verifier and compared.
 *
 * Sites come from the trusted parser's own AST (fragment-parse.mts), walked with
 * the same rule the verifier uses to decide what is an entry and what is an
 * expression (SourceClaimJson.functionSites / exprSites, in
 * verification/lean/Verification/ExperimentState/SourceClaimJson.lean). A site
 * is matched to a real TypeScript node by exact [start,end) span, and its type
 * comes from the checker. A type this tool cannot state as a calculus label is
 * omitted, never guessed: the omission, with the reason and the checker's own
 * rendering, goes to `<out>.omissions.json`, and the whole function is left out
 * of the claims document, since one missing site would fail extraction anyway.
 *
 * This producer is UNTRUSTED. The verifier checks what it claims.
 */
import {
  ElementFlags,
  SignatureKind,
  SymbolFlags,
  TypeFlags,
  isUnionType,
} from "typescript/unstable/sync";
import type { Checker, Symbol, Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type {
  BinaryExpression,
  Expression,
  FunctionDeclaration,
  FunctionLikeDeclaration,
  Identifier,
  Node,
  ParameterDeclaration,
  PropertyAccessExpression,
  PropertySignatureDeclaration,
  SignatureDeclaration,
  SourceFile,
  Statement,
  VariableDeclaration,
} from "typescript/unstable/ast";
import { writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { close, parseFile, projectFor } from "./fragment-parse.mts";
import type {
  ClaimType,
  FunctionClaims,
  NamedPoint,
  Row,
  SourceClaims,
} from "./source-claims.mts";
import type { Fields } from "./type-graph.mts";
import type { Ast, Expr, FunctionAst, Stmt } from "./fragment.mts";
import type { Span } from "./span.mts";
import { messageOf } from "./thrown.mts";

/* ------------------------------------------------------------- refusal -- */
// A type this producer will not state. The reason is a short slug; the
// rendering is the checker's own, so a reader can see what was refused.

class Refusal extends Error {
  readonly reason: string;
  readonly tsType: string;
  constructor(reason: string, tsType: string) {
    super(reason);
    this.reason = reason;
    this.tsType = tsType;
  }
}

/* ------------------------------------------- predicates the AST lacks -- */
// Written against `kind`, because that is all they ever were.

const FUNCTION_LIKE = new Set<number>([
  ts.SyntaxKind.FunctionDeclaration,
  ts.SyntaxKind.FunctionExpression,
  ts.SyntaxKind.ArrowFunction,
  ts.SyntaxKind.MethodDeclaration,
  ts.SyntaxKind.Constructor,
  ts.SyntaxKind.GetAccessor,
  ts.SyntaxKind.SetAccessor,
]);
const isFunctionLike = (n: Node): n is FunctionLikeDeclaration =>
  FUNCTION_LIKE.has(n.kind);
const isParameter = (n: Node): n is ParameterDeclaration =>
  n.kind === ts.SyntaxKind.Parameter;
const isPropertySignature = (n: Node): n is PropertySignatureDeclaration =>
  n.kind === ts.SyntaxKind.PropertySignature;

/* Everything that declares parameters, which is wider than the function-like
 * kinds above: a callable parameter's own type is a function type node, and its
 * optional parameters are what `arrowOf` refuses. */
const SIGNATURE_KINDS = new Set<number>([
  ...FUNCTION_LIKE,
  ts.SyntaxKind.CallSignature,
  ts.SyntaxKind.ConstructSignature,
  ts.SyntaxKind.MethodSignature,
  ts.SyntaxKind.IndexSignature,
  ts.SyntaxKind.FunctionType,
  ts.SyntaxKind.ConstructorType,
]);
const isSignatureDeclaration = (n: Node): n is SignatureDeclaration =>
  SIGNATURE_KINDS.has(n.kind);

/* ---------------------------------------------------------- the sites -- */
// Which spans carry a claim, from the trusted parse alone. The verifier
// refuses a claim anywhere else and requires one at each of these, so this
// walk mirrors `functionSites` in the Lean lowering exactly.

interface Sites {
  entries: Set<number>;
  exprs: Map<string, { pos: Span; kind: string }>;
}

function addExpr(out: Sites, pos: Span, kind: string): void {
  const key = pos[0] + ":" + pos[1];
  if (!out.exprs.has(key)) out.exprs.set(key, { pos, kind });
}

function walkExpr(e: Expr, out: Sites): void {
  switch (e.k) {
    case "id":
    case "lit":
      addExpr(out, e.pos, e.k);
      return;
    case "withValue":
      addExpr(out, e.pos, "withValue");
      walkExpr(e.fn, out);
      walkExpr(e.initial, out);
      return;
    case "alloc":
      addExpr(out, e.pos, e.k);
      for (const f of e.fields) walkExpr(f.e, out);
      return;
    case "functionTest":
    case "not":
    case "read":
      addExpr(out, e.pos, e.k);
      walkExpr(e.e, out);
      return;
    case "lambda":
      addExpr(out, e.pos, "lambda");
      walkExpr(e.body, out);
      return;
    case "write":
      addExpr(out, e.pos, "write");
      walkExpr(e.receiver, out);
      walkExpr(e.rhs, out);
      return;
    // Nullish assignment reads the LHS before deciding whether to write.
    case "nullishAssign":
      addExpr(out, e.pos, "nullishAssign");
      addExpr(out, e.namePos, "id");
      walkExpr(e.rhs, out);
      return;
    // Plain assignment names a location, without reading it.
    case "assign":
      addExpr(out, e.pos, "assign");
      walkExpr(e.rhs, out);
      return;
    case "bindWithReceiver":
    case "callWithReceiver":
      addExpr(out, e.pos, e.k);
      walkExpr(e.callee, out);
      walkExpr(e.receiver, out);
      for (const arg of e.args) walkExpr(arg, out);
      return;
    case "apply":
      addExpr(out, e.pos, "apply");
      walkExpr(e.callee, out);
      for (const arg of e.args) walkExpr(arg, out);
      return;
    case "bin":
      addExpr(out, e.pos, "bin");
      walkExpr(e.l, out);
      walkExpr(e.r, out);
      return;
    case "coalesce":
      addExpr(out, e.pos, "coalesce");
      walkExpr(e.left, out);
      walkExpr(e.right, out);
      return;
    case "conditional":
      // A source ternary: its own span is the expression claim.
      addExpr(out, e.pos, "conditional");
      walkExpr(e.cond, out);
      walkExpr(e.then, out);
      walkExpr(e.else_, out);
      return;
    case "ifBody":
      // A lowered statement-conditional inside a closure body: an entry.
      out.entries.add(e.pos[0]);
      walkExpr(e.cond, out);
      walkExpr(e.then, out);
      walkExpr(e.else_, out);
      return;
    case "seqBody":
    case "letBody":
      out.entries.add(e.pos[0]);
      walkExpr(e.init, out);
      walkExpr(e.body, out);
      return;
    case "returnBody":
      out.entries.add(e.pos[0]);
      walkExpr(e.e, out);
      return;
    case "doneBody":
      // Administrative completion; no source expression claim.
      return;
    default:
      // Every kind of the fragment is handled above, so this is reached only
      // by a tree the parser no longer writes the way this reads it.
      throw new Error("expression outside the lowered fragment");
  }
}

function walkStmt(s: Stmt, out: Sites): void {
  out.entries.add(s.pos[0]);
  switch (s.k) {
    case "break":
    case "continue":
      return;
    case "return":
    case "effect":
      walkExpr(s.e, out);
      return;
    case "const":
    case "let":
      // One entry for the statement; every declarator's initializer is a site.
      s.bindings.forEach((b) => walkExpr(b.init, out));
      return;
    case "while":
      // The loop head: the invariant candidate checked on entry and every
      // back edge.
      walkExpr(s.cond, out);
      s.body.forEach((st) => walkStmt(st, out));
      return;
    case "if":
      walkExpr(s.cond, out);
      s.then.forEach((st) => walkStmt(st, out));
      (s.else_ ?? []).forEach((st) => walkStmt(st, out));
      return;
    default:
      throw new Error("statement outside the lowered fragment");
  }
}

function functionSites(fn: FunctionAst): Sites {
  const out: Sites = { entries: new Set(), exprs: new Map() };
  fn.body.forEach((st) => walkStmt(st, out));
  return out;
}

/* ------------------------------------------------------- the AST index -- */
// A site's span, from the trusted parser's output, is matched to the compiler
// node with that same [getStart(sf), end) span: the checker speaks about
// nodes, the parser speaks about offsets, and this is the one place the two
// vocabularies meet.

const STATEMENT_KINDS = new Set<number>([
  ts.SyntaxKind.ReturnStatement,
  ts.SyntaxKind.VariableStatement,
  ts.SyntaxKind.IfStatement,
  ts.SyntaxKind.WhileStatement,
  ts.SyntaxKind.BreakStatement,
  ts.SyntaxKind.ContinueStatement,
  ts.SyntaxKind.ExpressionStatement,
]);

interface Indices {
  stmtByStart: Map<number, Statement>;
  exprBySpan: Map<string, Node>;
}

function buildIndices(sf: SourceFile): Indices {
  const stmtByStart = new Map<number, Statement>();
  const exprBySpan = new Map<string, Node>();
  const visit = (node: Node): void => {
    const start = node.getStart(sf);
    if (ts.isStatement(node) && STATEMENT_KINDS.has(node.kind) && !stmtByStart.has(start))
      stmtByStart.set(start, node);
    exprBySpan.set(start + ":" + node.end, node);
    node.forEachChild(visit);
  };
  visit(sf);
  return { stmtByStart, exprBySpan };
}

/* -------------------------------------------------- types into labels -- */
// The document's own type table: the four primitives, then one row per
// compound type on first use (SOURCE-CLAIMS.md). Rows are interned by exact
// content, so equal types always share a label.

function dedupSortInts(xs: number[]): number[] {
  return Array.from(new Set(xs)).sort((a, b) => a - b);
}
function arrCompare(a: number[], b: number[]): number {
  const n = Math.max(a.length, b.length);
  for (let i = 0; i < n; i++) {
    const x = a[i] ?? -Infinity;
    const y = b[i] ?? -Infinity;
    if (x !== y) return x - y;
  }
  return 0;
}
function dedupSortArrays(arrs: number[][]): number[][] {
  const sorted = arrs.map((a) => a.slice()).sort(arrCompare);
  const out: number[][] = [];
  for (const a of sorted)
    if (!out.length || arrCompare(out[out.length - 1], a) !== 0) out.push(a);
  return out;
}
function internRow(types: Row[], row: Row): number {
  const key = JSON.stringify(row);
  for (let i = 0; i < types.length; i++)
    if (JSON.stringify(types[i]) === key) return i;
  types.push(row);
  return types.length - 1;
}

/**
 * The bit pattern of the double a numeric literal denotes, which is the
 * identity the consumer's `numBits` assigns it: `1`, `1.0` and `1e0` are
 * one literal, and `-0` is `0`. Produced as a decimal string because the
 * consumer reads a `UInt64`.
 */
function numberBits(value: number): string {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, value === 0 ? 0 : value);
  return view.getBigUint64(0).toString();
}

/**
 * Numbers have no fixed rows, because the singletons are unbounded: each is
 * interned on use, exactly as the consumer interns them. Returns null when the
 * type is not a number or a union of numbers with primitives.
 */
function numberLabelsOf(type: Type, types: Row[]): number[] | null {
  const f = type.flags;
  if (type.isNumberLiteralType()) {
    if (!Number.isFinite(type.value)) return null;
    return [internRow(types, [{ numLit: { bits: numberBits(type.value) } }])];
  }
  if (f & TypeFlags.Number) return [internRow(types, ["num"])];
  if (isUnionType(type)) {
    const acc: number[] = [];
    for (const t of type.getTypes()) {
      const sub = primitiveLabelsOf(t) ?? numberLabelsOf(t, types);
      if (sub === null) return null;
      acc.push(...sub);
    }
    return dedupSortInts(acc);
  }
  return null;
}

/**
 * A type built only from null/true/false/undefined/boolean/never, as a sorted,
 * duplicate-free list of primitive labels, or null when the type (or some
 * union member) is none of those.
 */
function primitiveLabelsOf(type: Type): number[] | null {
  const f = type.flags;
  if (f & TypeFlags.Null) return [0];
  if (f & TypeFlags.Undefined) return [3];
  if (f & TypeFlags.Never) return [];
  if (f & TypeFlags.Boolean) return [1, 2]; // the `boolean` pseudo-union itself
  if (type.isBooleanLiteralType()) return type.value === true ? [1] : [2];
  if (isUnionType(type)) {
    const acc: number[] = [];
    for (const t of type.getTypes()) {
      const sub = primitiveLabelsOf(t);
      if (sub === null) return null;
      acc.push(...sub);
    }
    return dedupSortInts(acc);
  }
  return null;
}

/** A reading either succeeded and carries what it read, or it did not and
 * carries why — where it has a reason to give. */
type RecordRead =
  | { ok: true; fields: { name: string; type: Type }[] }
  | { ok: false; reason?: string };

/**
 * Record-shaped: at least one required, non-readonly property, no index
 * signatures, and not itself callable. `ok:false` with no reason means "not
 * object-shaped at all, try the arrow reading instead"; with a reason it means
 * "object-shaped but not this contract". A callable's bag reads the same way;
 * what makes it a bag is only that its own call signatures are not consulted.
 */
function tryRecord(type: Type, checker: Checker, callableBag = false): RecordRead {
  if (!(type.flags & TypeFlags.Object) && !callableBag) return { ok: false };
  if (
    (!callableBag && checker.getSignaturesOfType(type, SignatureKind.Call).length) ||
    checker.getSignaturesOfType(type, SignatureKind.Construct).length
  )
    return { ok: false };
  const props = checker.getPropertiesOfType(type);
  if (!props.length) return { ok: false, reason: "no-value-field" };
  if (checker.getIndexInfosOfType(type).length)
    return { ok: false, reason: "indexed-type" };
  const fields: { name: string; type: Type }[] = [];
  for (const prop of props) {
    if (prop.flags & SymbolFlags.Optional)
      return { ok: false, reason: "optional-field" };
    // A declaration arrives as a handle; `readonly` is on the node it names,
    // and the two kinds of member declaration that can carry one are these.
    const declaration = declarationOf(prop);
    if (
      declaration &&
      (isPropertySignature(declaration) || ts.isPropertyDeclaration(declaration)) &&
      declaration.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword)
    )
      return { ok: false, reason: "readonly-field" };
    fields.push({
      name: prop.name,
      type: must(checker.getTypeOfSymbol(prop), "field-type"),
    });
  }
  return { ok: true, fields };
}

type ArrowRead =
  | { ok: true; domains: Type[]; result: Type }
  | { ok: false; reason?: string };

/**
 * One signature with ordered required parameters, no
 * type parameters, no `this` parameter.
 */
function tryArrow(type: Type, checker: Checker): ArrowRead {
  const sigs = checker.getSignaturesOfType(type, SignatureKind.Call);
  if (sigs.length === 0) return { ok: false };
  if (
    sigs.length !== 1 ||
    checker.getSignaturesOfType(type, SignatureKind.Construct).length
  )
    return { ok: false, reason: "overloaded-arrow" };
  const sig = sigs[0];
  if (sig.typeParameters?.length) return { ok: false, reason: "generic-arrow" };
  if (sig.thisParameter !== undefined) return { ok: false, reason: "this-param" };
  let parameterCount = sig.parameters.length;
  let tail: Type[] = [];
  if (sig.hasRestParameter) {
    // Instantiated bind results use (...args: [A, B]) internally. Expand only
    // fixed required tuples; their syntax is not a variadic source contract.
    const symbol = sig.getParameters().at(-1);
    const rest = symbol && checker.getTypeOfSymbol(symbol);
    if (!rest?.isTypeReference()) return { ok: false, reason: "arrow-arity" };
    const target = rest.getTarget();
    if (!target.isTupleType()) return { ok: false, reason: "arrow-arity" };
    tail = [...checker.getTypeArguments(rest)];
    const flags = target.elementFlags ?? [];
    if (flags.length !== tail.length || target.fixedLength !== flags.length ||
        flags.some(flag => flag !== ElementFlags.Required))
      return { ok: false, reason: "arrow-arity" };
    parameterCount--;
  }
  // Optionality is on the declared parameter: a signature transports its
  // parameters as ids, and asking the checker for one of those symbols is
  // not the way to reach a type here — `getParameterType` is.
  const declared = sig.declaration?.resolve();
  if (
    declared &&
    isSignatureDeclaration(declared) &&
    declared.parameters.some((p) => p.questionToken || p.initializer)
  )
    return { ok: false, reason: "optional-param" };
  return {
    ok: true,
    domains: sig.parameters.slice(0, parameterCount).map((_, i) => must(checker.getParameterType(sig, i), "parameter-type")).concat(tail),
    result: must(checker.getReturnTypeOfSignature(sig), "return-type"),
  };
}

/**
 * The checker answers `undefined` where it has nothing to say. That is a site
 * this producer cannot state, like any other, so it becomes a refusal with its
 * own name rather than a crash somewhere further down.
 */
function must(type: Type | undefined, what: string): Type {
  if (!type) throw new Refusal(`no-${what}`, "");
  return type;
}

function basicReason(type: Type): string {
  const f = type.flags;
  if (f & TypeFlags.Void) return "void";
  if (f & (TypeFlags.String | TypeFlags.StringLiteral)) return "string";
  if (f & (TypeFlags.Number | TypeFlags.NumberLiteral)) return "number";
  if (f & TypeFlags.Any) return "any";
  if (f & TypeFlags.Unknown) return "unknown";
  if (f & TypeFlags.TypeParameter) return "generic";
  if (f & TypeFlags.Object) return "object-shape";
  return "unsupported-type";
}

/**
 * An intersection of record contracts, as `{first, rest}` (both sorted,
 * duplicate-free label lists), or null when the operands are not all records,
 * which leaves an arrow intersection still to try.
 */
function tryRecordIntersection(
  type: Type,
  checker: Checker,
  parts: readonly Type[],
  types: Row[],
  fuel: number,
): { first: Fields; rest: Fields[] } | null {
  const results = parts.map((t) => tryRecord(t, checker));
  const read = results.flatMap((r) => (r.ok ? [r] : []));
  if (read.length !== results.length) {
    const reason = refusals(results)[0];
    if (reason !== undefined) throw new Refusal(reason, checker.typeToString(type));
    return null;
  }
  const operands: Fields[] = [];
  for (const r of read) {
    const fs: Fields = r.fields.map((f): [string, number[]] =>
      [f.name, translateType(f.type, checker, types, false, fuel - 1)]);
    if (!operands.some((o) => JSON.stringify(o) === JSON.stringify(fs))) operands.push(fs);
  }
  operands.sort((a, b) => (JSON.stringify(a) < JSON.stringify(b) ? -1 : 1));
  const [first, ...rest] = operands;
  if (!first) throw new Refusal("record-operand", checker.typeToString(type));
  return { first, rest };
}

/** The reasons a list of readings gives, in order: a reading that refused
 * without one is "not this shape at all", which is not a refusal to report. */
const refusals = (results: (RecordRead | ArrowRead)[]): string[] =>
  results.flatMap((r) => (r.ok || r.reason === undefined ? [] : [r.reason]));

/** An intersection of arrows, in declaration order, exact repeats dropped. */
function tryArrowIntersection(
  type: Type,
  checker: Checker,
  parts: readonly Type[],
  types: Row[],
  fuel: number,
): [number[][], number[]][] | null {
  const results = parts.map((t) => tryArrow(t, checker));
  const read = results.flatMap((r) => (r.ok ? [r] : []));
  if (read.length !== results.length) {
    const reason = refusals(results)[0];
    if (reason !== undefined) throw new Refusal(reason, checker.typeToString(type));
    return null;
  }
  const arrows: [number[][], number[]][] = [];
  for (const r of read) {
    const pair: [number[][], number[]] = [
      r.domains.map((domain) => translateType(domain, checker, types, false, fuel - 1)),
      translateType(r.result, checker, types, false, fuel - 1),
    ];
    if (!arrows.some((a) => JSON.stringify(a) === JSON.stringify(pair)))
      arrows.push(pair);
  }
  return arrows;
}

// Arrow operands can contain further arrows, with bounded recursion for
// recursive TS types. Record fields admit the same primitive/callable operands.
function translateType(type: Type, checker: Checker, types: Row[], records = true, fuel = 64): number[] {
  if (fuel <= 0) throw new Refusal("type-depth", checker.typeToString(type));
  const prim = primitiveLabelsOf(type);
  if (prim !== null) return prim;
  const nums = numberLabelsOf(type, types);
  if (nums !== null) return nums;
  if (!records && (checker.getPropertiesOfType(type).length || checker.getIndexInfosOfType(type).length))
    throw new Refusal("callable-operand-properties", checker.typeToString(type));
  if (records && checker.getSignaturesOfType(type, SignatureKind.Call).length &&
      checker.getPropertiesOfType(type).length) {
    const bag = tryRecord(type, checker, true);
    if (!bag.ok) throw new Refusal(bag.reason || "callable-field", checker.typeToString(type));
    const arrow = tryArrow(type, checker);
    if (!arrow.ok) throw new Refusal(arrow.reason || "callable-signature", checker.typeToString(type));
    const P: Fields = bag.fields.map((f): [string, number[]] =>
      [f.name, translateType(f.type, checker, types, false, fuel - 1)]);
    const Ds = arrow.domains.map(D => translateType(D, checker, types, false, fuel - 1));
    const R = translateType(arrow.result, checker, types, false, fuel - 1);
    return [internRow(types, [{callable: {first: P, rest: [], arrows: [[Ds,R]]}}])];
  }
  if (type.isIntersectionType()) {
    const parts = type.getTypes();
    const refs = records ? tryRecordIntersection(type, checker, parts, types, fuel) : null;
    if (refs) return [internRow(types, [{ refs }])];
    const arrows = tryArrowIntersection(type, checker, parts, types, fuel);
    if (arrows) return [internRow(types, [{ arrs: { arrows } }])];
    throw new Refusal("mixed-intersection", checker.typeToString(type));
  }
  // A union is a label list, and the format admits one mixing cell and arrow
  // atoms with primitives, so each member contributes its own labels.
  if (isUnionType(type)) {
    const labels: number[] = [];
    for (const member of type.getTypes())
      labels.push(...translateType(member, checker, types, records, fuel - 1));
    return dedupSortInts(labels);
  }
  const rec = tryRecord(type, checker);
  if (rec.ok && !records) throw new Refusal("record-operand", checker.typeToString(type));
  if (rec.ok)
    return [
      internRow(types, [
        { refs: { first: rec.fields.map((f): [string, number[]] =>
            [f.name, translateType(f.type, checker, types, false, fuel - 1)]),
          rest: [] } },
      ]),
    ];
  if (rec.reason) throw new Refusal(rec.reason, checker.typeToString(type));
  const arr = tryArrow(type, checker);
  if (arr.ok) {
    const pair: [number[][], number[]] = [
      arr.domains.map((domain) => translateType(domain, checker, types, false, fuel - 1)),
      translateType(arr.result, checker, types, false, fuel - 1),
    ];
    return [internRow(types, [{ arrs: { arrows: [pair] } }])];
  }
  if (arr.reason) throw new Refusal(arr.reason, checker.typeToString(type));
  throw new Refusal(basicReason(type), checker.typeToString(type));
}

/* -------------------------------------------------- symbols and nodes -- */
// Remote objects are addressed by handle, so a declaration is fetched and a
// symbol is compared by id rather than by reference.

function declarationOf(sym: Symbol): Node | undefined {
  const handle = sym.valueDeclaration ?? sym.declarations?.[0];
  return handle ? handle.resolve() : undefined;
}

/* ------------------------------------------------ a site's own type -- */

/**
 * Object literals and arrow functions are contextually typed: the checker's
 * own type for the node is the narrowest branch it can infer on its own (one
 * record, or one signature), but a claim allocating into or implementing a
 * conjoined contract needs the wider annotation the value is held to. Prefer
 * that contextual type when it exists and translates. Under a union context,
 * use the checker's own expression type: an allocation constructs a cell and
 * a lambda implements an arrow. Its binding or return obligation checks the
 * enclosing union.
 * No union alternative is selected or discarded by this producer.
 *
 * Field reads have an invariant contract as well as a flow type. The latter
 * is an untrusted producer claim: entry assertions below expose the primitive
 * field predicates needed to check it against the heap.
 */
function readInvariant(
  node: PropertyAccessExpression,
  checker: Checker,
  types: Row[],
): number[] {
  const cellType = must(
    checker.getTypeAtLocation(node.expression),
    "receiver-type",
  );
  const cellLabels = translateType(cellType, checker, types);
  const named = (fs: Fields): number[] | null =>
    fs.find((f) => f[0] === node.name.text)?.[1] ?? null;
  if (cellLabels.length === 1) {
    const row = types[cellLabels[0]];
    const clause = Array.isArray(row) && row.length === 1 ? row[0] : null;
    if (clause !== null && typeof clause === "object") {
      if ("refs" in clause) {
        const labels = named(clause.refs.first);
        if (labels) return labels;
      }
      if ("callable" in clause) {
        const labels = named(clause.callable.first);
        if (labels) return labels;
      }
    }
  }
  throw new Refusal("read-of-non-reference", checker.typeToString(cellType));
}

/** Keep the invariant when the surrounding contract already asks for it.
 * In particular, a write from an explicitly widened const only establishes
 * that const's exported contract, even if TS folds its initializer to a unit. */
function readLabels(
  node: PropertyAccessExpression,
  checker: Checker,
  types: Row[],
): number[] {
  const invariant = readInvariant(node, checker, types);
  const context = checker.getContextualType(node);
  if (context) {
    try {
      if (
        JSON.stringify(translateType(context, checker, types)) ===
        JSON.stringify(invariant)
      )
        return invariant;
    } catch (error) {
      if (!(error instanceof Refusal)) throw error;
    }
  }
  return translateType(
    must(checker.getTypeAtLocation(node), "read-type"),
    checker,
    types,
  );
}

/**
 * TypeScript folds a boolean local declared with a wider annotation but a
 * literal initializer (`const condition: boolean = true;`) back to that
 * literal, and then marks whichever arm of `if (condition)` the literal rules
 * out as unreachable — every reference there reads back as `never`. The
 * calculus does not fold constants across a test: `if`/`while` on a bare name
 * or its negation (`conditionVariable`, SourceExtraction.lean) narrows the
 * tested binding to `true`/`false` in the corresponding arm regardless of its
 * initializer, and both arms stay live. So `never` on a reference to a local
 * is never trusted outright — it is TypeScript proving more than the
 * calculus's model of this one test does, not a fact the calculus can use.
 */
function testedIdentitySymbol(
  cond: Expression,
  checker: Checker,
): { sym: Symbol; negated: boolean } | null {
  if (ts.isParenthesizedExpression(cond))
    return testedIdentitySymbol(cond.expression, checker);
  if (
    ts.isPrefixUnaryExpression(cond) &&
    cond.operator === ts.SyntaxKind.ExclamationToken
  ) {
    const inner = testedIdentitySymbol(cond.operand, checker);
    return inner && { sym: inner.sym, negated: !inner.negated };
  }
  if (ts.isIdentifier(cond)) {
    const sym = checker.getSymbolAtLocation(cond);
    return sym ? { sym, negated: false } : null;
  }
  return null;
}

/**
 * Walks outward from a reference through enclosing `if`/`while` statements,
 * applying the innermost one that tests this same binding by bare identity.
 */
function truthyGuardLabels(
  node: Node,
  checker: Checker,
  anchor: Node = node,
): number[] | null {
  const sym = checker.getSymbolAtLocation(node);
  if (!sym) return null;
  let child: Node = anchor;
  let cur: Node = anchor.parent;
  while (cur && !isFunctionLike(cur)) {
    if (ts.isIfStatement(cur) || ts.isWhileStatement(cur)) {
      const tested = testedIdentitySymbol(cur.expression, checker);
      if (tested && tested.sym.id === sym.id) {
        const truthyArm = ts.isIfStatement(cur)
          ? child === cur.thenStatement
          : child === cur.statement;
        const falsyArm = ts.isIfStatement(cur) && child === cur.elseStatement;
        if (truthyArm) return tested.negated ? [2] : [1];
        if (falsyArm) return tested.negated ? [1] : [2];
      }
    }
    child = cur;
    cur = cur.parent;
  }
  return null;
}

/** A strict null, undefined or function-shape test on an immutable identifier. */
function testedTagSymbol(cond: Expression, checker: Checker, types: Row[]): {sym: Symbol; equal: boolean; label: number | "function"} | null {
  if (ts.isParenthesizedExpression(cond)) return testedTagSymbol(cond.expression, checker, types);
  if (ts.isPrefixUnaryExpression(cond) && cond.operator === ts.SyntaxKind.ExclamationToken) {
    const inner = testedTagSymbol(cond.operand, checker, types);
    return inner && {...inner, equal: !inner.equal};
  }
  if (!ts.isBinaryExpression(cond)) return null;
  const op = cond.operatorToken.kind;
  if (op !== ts.SyntaxKind.EqualsEqualsEqualsToken && op !== ts.SyntaxKind.ExclamationEqualsEqualsToken) return null;
  const unwrap = (e: Expression): Expression => ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e;
  const l = unwrap(cond.left), r = unwrap(cond.right);
  const typeOf = ts.isTypeOfExpression(l) && ts.isStringLiteral(r) && r.text === "function"
    ? l : ts.isTypeOfExpression(r) && ts.isStringLiteral(l) && l.text === "function" ? r : null;
  if (typeOf) {
    const id = unwrap(typeOf.expression);
    const sym = ts.isIdentifier(id) ? checker.getSymbolAtLocation(id) : null;
    return sym ? {sym, equal: op === ts.SyntaxKind.EqualsEqualsEqualsToken, label: "function"} : null;
  }
  const unitLabel = (node: Expression): number | null => {
    const type = checker.getTypeAtLocation(node);
    const flags = type?.flags ?? 0;
    if (flags & TypeFlags.Null) return 0;
    if (flags & TypeFlags.Undefined) return 3;
    if (type?.isNumberLiteralType() && Number.isFinite(type.value))
      return internRow(types, [{ numLit: { bits: numberBits(type.value) } }]);
    return null;
  };
  const left = unitLabel(cond.left), right = unitLabel(cond.right);
  const id = left !== null ? cond.right : right !== null ? cond.left : null;
  const label = left ?? right;
  if (!id || !ts.isIdentifier(id) || label === null) return null;
  const sym = checker.getSymbolAtLocation(id);
  return sym ? {sym, equal: op === ts.SyntaxKind.EqualsEqualsEqualsToken, label} : null;
}

function alwaysReturns(stmt: Statement): boolean {
  if (ts.isReturnStatement(stmt)) return true;
  if (ts.isBlock(stmt)) return stmt.statements.some(alwaysReturns);
  return ts.isIfStatement(stmt) && !!stmt.elseStatement &&
    alwaysReturns(stmt.thenStatement) && alwaysReturns(stmt.elseStatement);
}

/** Refine a fixed binding contract only along explicit null/undefined/function-test edges.
 * A preceding returning arm establishes the opposite edge for its continuation.
 * Immutable const captures retain creation-time guards across arrow functions;
 * parameters and other function boundaries stop the walk. */
function tagGuardLabels(node: Node, checker: Checker, types: Row[], labels: number[], anchor: Node = node): number[] {
  const sym = checker.getSymbolAtLocation(node);
  if (!sym) return labels;
  const declaration = declarationOf(sym);
  const immutableCapture = declaration && ts.isVariableDeclaration(declaration) &&
    ts.isVariableDeclarationList(declaration.parent) &&
    (declaration.parent.flags & ts.NodeFlags.Const) !== 0;
  const refine = (cond: Expression, truth: boolean, base: number[]): number[] => {
    if (ts.isParenthesizedExpression(cond)) return refine(cond.expression, truth, base);
    if (ts.isPrefixUnaryExpression(cond) && cond.operator === ts.SyntaxKind.ExclamationToken)
      return refine(cond.operand, !truth, base);
    if (ts.isBinaryExpression(cond)) {
      const op = cond.operatorToken.kind;
      if (op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken) {
        const and = op === ts.SyntaxKind.AmpersandAmpersandToken;
        // True conjunctions and false disjunctions establish both operands.
        if (truth === and) return refine(cond.right, truth, refine(cond.left, truth, base));
        // The other outcome can come from either short-circuit path. Preserve
        // their union; a fact from just one path cannot refine the whole edge.
        return dedupSortInts([
          ...refine(cond.left, truth, base),
          ...refine(cond.right, truth, refine(cond.left, !truth, base)),
        ]);
      }
    }
    const test = testedTagSymbol(cond, checker, types);
    if (test?.sym.id !== sym.id) return base;
    if (typeof test.label === "number" && types[test.label]?.some((c) =>
        typeof c === "object" && "numLit" in c)) {
      const singleton = test.label;
      // A broad number can equal this singleton. Its positive branch narrows
      // to the singleton; the negative branch cannot subtract it from `number`.
      return dedupSortInts(base.flatMap((label) => types[label]?.includes("num")
        ? [test.equal === truth ? singleton : label]
        : (label === singleton) === (test.equal === truth) ? [label] : []));
    }
    return base.filter((label) => (test.label === "function"
      ? (types[label]?.some((clause) =>
          (clause !== null && typeof clause === "object" && ("arrs" in clause || "callable" in clause)) === (test.equal === truth)) ?? true)
      : (label === test.label) === (test.equal === truth)));

  };
  const apply = (cond: Expression, truth: boolean) => { labels = refine(cond, truth, labels); };
  let child: Node = anchor, cur: Node = anchor.parent;
  while (cur) {
    if (isFunctionLike(cur) && !(immutableCapture && ts.isArrowFunction(cur))) break;
    if (ts.isIfStatement(cur)) {
      if (child === cur.thenStatement) apply(cur.expression, true);
      if (child === cur.elseStatement) apply(cur.expression, false);
    } else if (ts.isWhileStatement(cur) && child === cur.statement) {
      apply(cur.expression, true);
    } else if (ts.isConditionalExpression(cur)) {
      if (child === cur.whenTrue) apply(cur.condition, true);
      if (child === cur.whenFalse) apply(cur.condition, false);
    } else if (ts.isBinaryExpression(cur) && child === cur.right) {
      if (cur.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) apply(cur.left, true);
      if (cur.operatorToken.kind === ts.SyntaxKind.BarBarToken) apply(cur.left, false);
    } else if (ts.isBlock(cur)) {
      for (const stmt of cur.statements) {
        if (stmt === child) break;
        if (ts.isIfStatement(stmt)) {
          if (alwaysReturns(stmt.thenStatement)) apply(stmt.expression, false);
          if (stmt.elseStatement && alwaysReturns(stmt.elseStatement)) apply(stmt.expression, true);
        }
      }
    }
    child = cur;
    cur = cur.parent;
  }
  return labels;
}

/**
 * The general fallback once `never` is rejected: the binding's own declared
 * type, ignoring flow entirely. Always sound, since it is what every value the
 * binding could ever hold is required to satisfy.
 */
function declaredTypeAt(node: Node, checker: Checker, types: Row[]): number[] {
  const sym = checker.getSymbolAtLocation(node);
  if (sym)
    return translateType(
      must(checker.getTypeOfSymbol(sym), "binding-type"),
      checker,
      types,
    );
  throw new Refusal("unreachable-per-typescript", "never");
}

/** A binding's reading, memoised for one function. Keyed by declaration start. */
interface Authoritative {
  labels: number[] | null;
  readTainted: boolean;
  declared: number[] | null;
  claimed: number[] | null;
}
type DeclCache = Map<number, Authoritative>;

function isMutableDeclaration(decl: Node | undefined): boolean {
  return !!decl &&
    ts.isVariableDeclaration(decl) &&
    ts.isVariableDeclarationList(decl.parent) &&
    (decl.parent.flags & ts.NodeFlags.Const) === 0;
}

/**
 * The one place every reference to a local binding is priced: a real guard
 * wins outright (it is what the calculus itself would derive); failing that, a
 * binding already known to disagree with TypeScript about its own value
 * (`authoritativeType`) uses that fixed reading instead of asking flow at all;
 * only a plain, untainted local defers to TypeScript's own answer, with
 * `never` still rejected in favour of the declared type, since it is always
 * TypeScript proving a stronger fact than a test the calculus has no rule for
 * is entitled to.
 */
function bestLabelsForReference(
  node: Identifier,
  checker: Checker,
  types: Row[],
  declCache: DeclCache | null,
  sf: SourceFile,
): number[] {
  const symbol = checker.getSymbolAtLocation(node);
  if (symbol && isMutableDeclaration(declarationOf(symbol))) {
    // A mutable read describes this point's contents. Neither an initializer
    // cache nor a syntactic guard survives arbitrary intervening writes.
    return translateType(
      must(checker.getTypeAtLocation(node), "reference-type"), checker, types,
    );
  }
  const guard = truthyGuardLabels(node, checker);
  if (guard) return guard;
  if (declCache && symbol) {
    const decl = declarationOf(symbol);
    if (decl && (ts.isVariableDeclaration(decl) || isParameter(decl))) {
      const auth = authoritativeType(
        { decl, name: node.text, sym: symbol },
        checker,
        types,
        declCache,
        sf,
      );
      // A tainted binding (read- or literal-tainted; see `authoritativeType`)
      // is wrong everywhere but a matching guard: the calculus's own internal
      // value for it is its fixed reading (a read's exported type, or a
      // `const`'s declared annotation — the cast a `const` compiles to, never
      // the narrower literal TypeScript tracks for it), so a claim anywhere
      // has to be provable from that, not from whatever TypeScript
      // additionally happens to know. A matching guard is the one exception,
      // already returned above — the one place the compiled program itself
      // narrows the binding's own internal value, exactly enough to justify
      // the arm's tighter claim.
      // A binding with no fixed reading of its own — a parameter, a mutable
      // local — is neither tainted nor differently declared, so the guard below
      // is the same condition it always was.
      if (
        auth.labels &&
        (auth.readTainted ||
          (auth.declared &&
            JSON.stringify(auth.declared) !== JSON.stringify(auth.claimed)))
      )
        return tagGuardLabels(node, checker, types, auth.labels);
    }
  }
  const t = must(checker.getTypeAtLocation(node), "reference-type");
  if (t.flags & TypeFlags.Never)
    return declaredTypeAt(node, checker, types);
  return translateType(t, checker, types);
}

function declarationExprKind(node: Expression): string {
  if (ts.isParenthesizedExpression(node))
    return declarationExprKind(node.expression);
  if (ts.isPropertyAccessExpression(node)) return "read";
  if (ts.isObjectLiteralExpression(node)) return "alloc";
  if (ts.isArrowFunction(node)) return "lambda";
  return "other";
}

/**
 * A read snapshot retains its initializer's claimed type independently of
 * later heap mutations. An explicitly wider annotation remains the ceiling
 * used by this producer, including on paths TypeScript treats as unreachable.
 *
 * Parameters and mutable locals have no fixed initializer-based reading.
 * Neither does a plain `const` TypeScript does not narrow past its declaration.
 */
function authoritativeType(
  binding: { decl: VariableDeclaration | ParameterDeclaration; name: string; sym: Symbol },
  checker: Checker,
  types: Row[],
  cache: DeclCache,
  sf: SourceFile,
): Authoritative {
  const key = binding.decl.getStart(sf);
  const hit = cache.get(key);
  if (hit) return hit;
  let result: Authoritative;
  if (isParameter(binding.decl) || isMutableDeclaration(binding.decl)) {
    result = { labels: null, readTainted: false, declared: null, claimed: null };
  } else {
    const init = binding.decl.initializer;
    // Everything without one is a parameter or a mutable local, taken above: a
    // `const` the compiler accepted has an initializer.
    if (!init) throw new Refusal("no-initializer", binding.name);
    const kind = declarationExprKind(init);
    const claimed = typeForExprSite(kind, init, checker, types, cache, sf);
    let declared: number[] | null = null;
    if (binding.decl.type) {
      try {
        declared = translateType(
          must(checker.getTypeFromTypeNode(binding.decl.type), "annotation-type"),
          checker,
          types,
        );
      } catch {
        declared = null;
      }
    }
    const literalTaint =
      declared !== null && JSON.stringify(declared) !== JSON.stringify(claimed);
    result = {
      labels: literalTaint ? declared : claimed,
      readTainted: kind === "read",
      declared,
      claimed,
    };
  }
  cache.set(key, result);
  return result;
}

/**
 * Mirrors the JSON `k` tags the parser assigns, over a real node, for the one
 * place a real node needs re-classifying: a write's own value.
 */
function tsExprKind(node: Expression): string {
  if (ts.isParenthesizedExpression(node)) return tsExprKind(node.expression);
  if (ts.isIdentifier(node)) return "id";
  if (
    node.kind === ts.SyntaxKind.NullKeyword ||
    node.kind === ts.SyntaxKind.TrueKeyword ||
    node.kind === ts.SyntaxKind.FalseKeyword
  )
    return "lit";
  if (ts.isPropertyAccessExpression(node)) return "read";
  if (ts.isObjectLiteralExpression(node)) return "alloc";
  if (ts.isArrowFunction(node)) return "lambda";
  if (
    ts.isBinaryExpression(node) &&
    node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
    ts.isPropertyAccessExpression(node.left)
  )
    return "write";
  return "other";
}

/** The node at a site is the one the trusted parser classified, so a kind that
 * does not match the tree is the two disagreeing — a refusal, not a crash. */
function asKind<T extends Node>(
  node: Node,
  is: (n: Node) => n is T,
  kind: string,
): T {
  if (!is(node)) throw new Refusal("site-kind-mismatch", kind);
  return node;
}

function typeForExprSite(
  kind: string,
  node: Node,
  checker: Checker,
  types: Row[],
  declCache: DeclCache | null,
  sf: SourceFile,
): number[] {
  if (kind === "read") {
    return readLabels(asKind(node, ts.isPropertyAccessExpression, kind), checker, types);
  }
  if (kind === "id")
    return bestLabelsForReference(
      asKind(node, ts.isIdentifier, kind),
      checker,
      types,
      declCache,
      sf,
    );
  // JavaScript's assignment expression evaluates to the assigned value, and
  // the calculus's write carries that same value forward as the expression's
  // result (SourceExtraction.lean's `.write` case derives the write node's
  // type from the right-hand side's own claim, not from asking separately
  // what the assignment evaluates to) — so the write's claim has to be
  // exactly the right-hand side's claim, not a second, independently-asked
  // opinion that could disagree with it.
  if (kind === "write" || kind === "assign") {
    let assignment: Expression = asKind(node, ts.isExpression, kind);
    while (ts.isParenthesizedExpression(assignment))
      assignment = assignment.expression;
    const rhs = asKind(assignment, ts.isBinaryExpression, kind).right;
    return typeForExprSite(tsExprKind(rhs), rhs, checker, types, declCache, sf);
  }
  if (kind === "alloc" || kind === "lambda") {
    const ctx = checker.getContextualType(asKind(node, ts.isExpression, kind));
    if (ctx && !isUnionType(ctx)) {
      try {
        return translateType(ctx, checker, types);
      } catch {
        /* fall through to the node's own type */
      }
    }
  }
  return translateType(
    must(checker.getTypeAtLocation(node), "expression-type"),
    checker,
    types,
  );
}

/* ------------------------------------------------- entry environments -- */
// The environment at an entry is every parameter and enclosing-block `const`
// declared before it (SOURCE-CLAIMS.md), independent of control flow. The
// fragment's scope rule is small enough to read straight off the tree, which
// is also the only place that knows the textual order the rule depends on.

interface VisibleBinding {
  sym: Symbol;
  decl: VariableDeclaration | ParameterDeclaration;
  declStart: number;
  name: string;
}

function envAtEntry(
  anchorNode: Node,
  offset: number,
  checker: Checker,
  sf: SourceFile,
): VisibleBinding[] {
  const seen: VisibleBinding[] = [];
  const take = (
    nameNode: Identifier,
    decl: VariableDeclaration | ParameterDeclaration,
  ): void => {
    const declStart = nameNode.getStart(sf);
    if (declStart >= offset) return;
    const sym = checker.getSymbolAtLocation(nameNode);
    if (sym) seen.push({ sym, decl, declStart, name: nameNode.text });
  };
  for (let n: Node = anchorNode; n; n = n.parent) {
    if (ts.isBlock(n) || ts.isSourceFile(n)) {
      for (const st of n.statements)
        if (ts.isVariableStatement(st))
          for (const d of st.declarationList.declarations)
            if (ts.isIdentifier(d.name)) take(d.name, d);
    }
    // Every enclosing function contributes its parameters, not just the
    // innermost: an entry inside a lowered closure body still sees the
    // parameters of the function that closure was written in.
    if (isFunctionLike(n))
      for (const p of n.parameters)
        if (ts.isIdentifier(p.name)) take(p.name, p);
  }
  seen.sort((a, b) => a.declStart - b.declStart);
  return seen;
}

/**
 * The real expression, if any, whose flow this entry's own statement is keyed
 * on: the condition for `if`/`while`, the initializer for `const`, the
 * statement's own expression otherwise. Restricting the search to this
 * expression (rather than the whole statement, which for `if`/`while` would
 * reach into branches decided *after* this point) keeps the anchor at the
 * right point in the control-flow graph.
 */
function anchorSearchScope(stmtNode: Statement): Expression | null {
  if (ts.isIfStatement(stmtNode) || ts.isWhileStatement(stmtNode))
    return stmtNode.expression;
  if (ts.isReturnStatement(stmtNode)) return stmtNode.expression ?? null;
  if (ts.isVariableStatement(stmtNode))
    return stmtNode.declarationList.declarations[0].initializer ?? null;
  if (ts.isExpressionStatement(stmtNode)) return stmtNode.expression;
  return null; // break/continue: no expression to anchor on
}

/** Reads at the entry's evaluation point, before any effects or branch choice.
 * Do not descend into closure bodies, call arguments, or a binary RHS: their
 * flow types can describe a later state. Unsupported anchors carry no facts.
 * These are claims only; the verifier must establish each predicate. */
function entryFieldClaims(
  stmt: Statement,
  binding: VisibleBinding,
  checker: Checker,
  types: Row[],
): NamedPoint["current"] {
  let node = anchorSearchScope(stmt);
  while (node) {
    if (
      ts.isParenthesizedExpression(node) ||
      ts.isPrefixUnaryExpression(node)
    ) {
      node = ts.isParenthesizedExpression(node)
        ? node.expression
        : node.operand;
    } else if (
      ts.isBinaryExpression(node) &&
      (node.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken ||
        node.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsEqualsToken)
    ) {
      node = node.left;
    } else break;
  }
  if (
    !node ||
    !ts.isPropertyAccessExpression(node) ||
    !ts.isIdentifier(node.expression) ||
    checker.getSymbolAtLocation(node.expression) !== binding.sym
  )
    return null;
  const labels = readLabels(node, checker, types);
  if (
    JSON.stringify(labels) ===
    JSON.stringify(readInvariant(node, checker, types))
  )
    return null;
  // Heap knowledge supports primitive predicates, not arbitrary graph types.
  if (
    !labels.every((label) =>
      types[label].every(
        (clause) =>
          clause === "nul" ||
          clause === "undef" ||
          clause === "bool" ||
          clause === "num" ||
          (typeof clause === "object" &&
            ("numLit" in clause || "boolLit" in clause)),
      ),
    )
  )
    return null;
  return [[node.name.text, labels]];
}

function isNamePosition(id: Node): boolean {
  const p = id.parent;
  if (!p) return false;
  return (
    (ts.isPropertyAccessExpression(p) ||
      isPropertySignature(p) ||
      ts.isPropertyAssignment(p) ||
      isParameter(p) ||
      ts.isVariableDeclaration(p) ||
      ts.isBindingElement(p)) &&
    p.name === id
  );
}

function findNameRef(scope: Node | null, name: string): Identifier | null {
  if (!scope) return null;
  let found: Identifier | null = null;
  const visit = (node: Node): void => {
    if (found) return;
    if (ts.isIdentifier(node) && node.text === name && !isNamePosition(node)) {
      found = node;
      return;
    }
    node.forEachChild(visit);
  };
  visit(scope);
  return found;
}

/**
 * `getTypeOfSymbolAtLocation` only narrows when its location is itself a
 * reference resolving to that symbol; given any other node it falls back to
 * the symbol's plain declared type. So: when the entry's own anchoring
 * expression mentions this binding, use that reference directly (it narrows
 * like any other identifier); otherwise fall back to the declared type, which
 * is always sound, if not always precise enough for proof search.
 */
function bindingLabelsAtEntry(
  stmtNode: Statement,
  binding: VisibleBinding,
  checker: Checker,
  sf: SourceFile,
  types: Row[],
  cache: DeclCache,
): number[] {
  const ref = findNameRef(anchorSearchScope(stmtNode), binding.name);
  if (ref) return bestLabelsForReference(ref, checker, types, cache, sf);
  // Absence from the statement does not undo the contract imposed at the
  // declaration. Apply only guards that dominate this statement's entry.
  const auth = authoritativeType(binding, checker, types, cache, sf);
  // An immutable snapshot keeps an enclosing Boolean guard even when this
  // statement does not mention it. Calls can change its source cell, not the
  // saved value. Mutable bindings have no authoritative initializer contract.
  if (auth.labels) {
    const guard = truthyGuardLabels(binding.decl.name, checker, stmtNode);
    if (guard) return guard;
  }
  if (auth.labels && (auth.readTainted || (auth.declared && JSON.stringify(auth.declared) !== JSON.stringify(auth.claimed))))
    return tagGuardLabels(binding.decl.name, checker, types, auth.labels, stmtNode);
  return translateType(
    must(checker.getTypeOfSymbolAtLocation(binding.sym, stmtNode), "binding-type"),
    checker,
    types,
  );
}

/* -------------------------------------------------------------- driver -- */

interface Omission {
  function: string;
  site: unknown;
  tsType: string;
  reason: string;
}

function omissionRecord(fn: string, site: unknown, err: unknown): Omission {
  return {
    function: fn,
    site,
    tsType: err instanceof Refusal ? err.tsType : "",
    reason:
      err instanceof Refusal
        ? err.reason
        : messageOf(err),
  };
}

/** A parameter's own name. The trusted parse refuses a destructuring pattern
 * before this producer ever sees the file, so one here is the two disagreeing. */
function parameterName(p: ParameterDeclaration): string {
  if (!ts.isIdentifier(p.name))
    throw new Refusal("destructuring-parameter", printName(p.name));
  return p.name.text;
}
const printName = (name: Node): string =>
  ts.isIdentifier(name) ? name.text : "";

/** Rigid references are scoped to this declaration; names are emitted only
 * after matching the compiler symbol identity, never by printed type text. */
function processGenericFunction(fn: FunctionAst, node: FunctionDeclaration, checker: Checker,
  sf: SourceFile, types: Row[], indices: Indices): FunctionClaims {
  const parameters = new Map<number, string>();
  for (const p of node.typeParameters ?? []) {
    const symbol = checker.getSymbolAtLocation(p.name);
    if (!symbol) throw new Refusal("generic-parameter-symbol", p.name.text);
    parameters.set(symbol.id, p.name.text);
  }
  const claim = (t: Type): ClaimType => {
    if (t.flags & TypeFlags.TypeParameter) {
      const symbol = t.getSymbol();
      const name = symbol && parameters.get(symbol.id);
      if (!name) throw new Refusal("out-of-scope-type-parameter", checker.typeToString(t));
      return {param: name};
    }
    return translateType(t, checker, types);
  };
  const at = (n: Node) => claim(must(checker.getTypeAtLocation(n), "generic-site-type"));
  const sites = functionSites(fn);
  const sig = checker.getSignatureFromDeclaration(node);
  if (!sig) throw new Refusal("no-signature", "");
  return {
    name: fn.name, namePos: fn.namePos,
    params: node.parameters.map((p) => ({name:parameterName(p),type:at(p.name),current:null})),
    result: claim(must(checker.getReturnTypeOfSignature(sig), "return-type")),
    entries: [...sites.entries].sort((a,b)=>a-b).map(start => {
      const stmt = indices.stmtByStart.get(start);
      if (!stmt) throw new Refusal("site-not-found", "");
      return {start, bindings:envAtEntry(stmt,start,checker,sf).map(b=>({
        name:b.name, type:claim(must(checker.getTypeOfSymbolAtLocation(b.sym,stmt),"binding-type")),current:null,
      }))};
    }),
    expressions:[...sites.exprs].map(([key,{pos}])=> {
      const expression=indices.exprBySpan.get(key);
      if (!expression) throw new Refusal("site-not-found", "");
      return {pos,type:at(expression),current:null};
    }),
  };
}

function processFunction(
  fnJson: FunctionAst,
  fnNode: FunctionDeclaration,
  checker: Checker,
  sf: SourceFile,
  types: Row[],
  indices: Indices,
  omissions: Omission[],
): FunctionClaims | null {
  if (fnNode.typeParameters?.length) return processGenericFunction(fnJson,fnNode,checker,sf,types,indices);
  const before = omissions.length;
  const name = fnJson.name;
  const params: (NamedPoint | null)[] = fnNode.parameters.map((p) => {
    try {
      return {
        name: parameterName(p),
        type: translateType(
          must(checker.getTypeAtLocation(p.name), "parameter-type"),
          checker,
          types,
        ),
        current: null,
      };
    } catch (e) {
      omissions.push(
        omissionRecord(name, { kind: "param", name: printName(p.name) }, e),
      );
      return null;
    }
  });

  let result: number[] | null = null;
  try {
    const sig = checker.getSignatureFromDeclaration(fnNode);
    if (!sig) throw new Refusal("no-signature", "");
    result = translateType(
      must(checker.getReturnTypeOfSignature(sig), "return-type"),
      checker,
      types,
    );
  } catch (e) {
    omissions.push(omissionRecord(name, { kind: "result" }, e));
  }

  const sites = functionSites(fnJson); // may throw; the caller catches
  const declCache: DeclCache = new Map(); // one function's memo

  const entries: FunctionClaims["entries"] = [];
  for (const start of Array.from(sites.entries).sort((a, b) => a - b)) {
    const stmtNode = indices.stmtByStart.get(start);
    if (!stmtNode) {
      omissions.push(
        omissionRecord(name, { kind: "entry", start }, new Refusal("site-not-found", "")),
      );
      continue;
    }
    const bindings: FunctionClaims["entries"][number]["bindings"] = [];
    for (const b of envAtEntry(stmtNode, start, checker, sf)) {
      try {
        bindings.push({
          name: b.name,
          type: bindingLabelsAtEntry(stmtNode, b, checker, sf, types, declCache),
          current: entryFieldClaims(stmtNode, b, checker, types),
        });
      } catch (e) {
        omissions.push(
          omissionRecord(name, { kind: "entry", start, name: b.name }, e),
        );
      }
    }
    entries.push({ start, bindings });
  }

  const expressions: FunctionClaims["expressions"] = [];
  for (const [key, { pos, kind }] of Array.from(sites.exprs.entries()).sort(
    (a, b) => a[1].pos[0] - b[1].pos[0],
  )) {
    const node = indices.exprBySpan.get(key);
    if (!node) {
      omissions.push(
        omissionRecord(name, { kind: "expr", pos }, new Refusal("site-not-found", "")),
      );
      continue;
    }
    try {
      expressions.push({
        pos,
        type: typeForExprSite(kind, node, checker, types, declCache, sf),
        current: null,
      });
    } catch (e) {
      omissions.push(omissionRecord(name, { kind: "expr", pos }, e));
    }
  }

  // One unstated site would fail extraction, so a function is claimed whole or
  // not at all.
  const stated = params.filter((p) => p !== null);
  if (omissions.length !== before || result === null || stated.length !== params.length)
    return null;
  return {
    name: fnJson.name,
    namePos: fnJson.namePos,
    params: stated,
    result,
    entries,
    expressions,
  };
}

/* ------------------------------------------------------------ produce -- */

export interface Produced {
  doc: SourceClaims;
  omissions: Omission[];
  ast: Ast;
  /** The checker's own verdict, per function: what `tsc --noEmit` would say. */
  accepted: Map<string, boolean>;
}

export { close };

export function produce(file: string): Produced {
  const ast = parseFile(file); // the trusted parse; also the syntactic gate
  const absolute = resolve(file);
  // The same project, in the same compiler process, the gate just parsed
  // under: one `tsconfig.json` covering the corpus means the 2nd file
  // onwards costs nothing to open.
  const project = projectFor(absolute);
  // What every claim below is relative to. A file typed under a laxer regime
  // would be stating types the corpus's own configuration does not support,
  // so it is refused rather than silently claimed.
  if (!project.compilerOptions.strict)
    throw new Error(
      `${file} is not covered by a tsconfig.json with "strict": true`,
    );
  const checker = project.checker;
  const sf = project.program.getSourceFile(absolute);
  if (!sf) throw new Error(`the compiler produced no tree for ${file}`);
  const indices = buildIndices(sf);
  const fnNodes = sf.statements.filter(ts.isFunctionDeclaration);
  if (fnNodes.length !== ast.functions.length)
    throw new Error(
      "function count mismatch between the trusted parse and the checker's program",
    );

  const types: Row[] = [
    ["nul"],
    [{ boolLit: { value: true } }],
    [{ boolLit: { value: false } }],
    ["undef"],
  ];
  const omissions: Omission[] = [];
  const functions: FunctionClaims[] = [];
  ast.functions.forEach((fnJson, i) => {
    const before = types.length;
    try {
      const built = processFunction(
        fnJson,
        fnNodes[i],
        checker,
        sf,
        types,
        indices,
        omissions,
      );
      if (built) functions.push(built);
      else types.length = before; // only a kept function's rows stay
    } catch (e) {
      types.length = before;
      omissions.push(omissionRecord(fnJson.name, { kind: "function" }, e));
    }
  });

  // A diagnostic belongs to the function whose span contains it, so one bad
  // function does not speak for the rest of the file.
  const diagnostics = [
    ...project.program.getSyntacticDiagnostics(absolute),
    ...project.program.getSemanticDiagnostics(absolute),
  ];
  const accepted = new Map<string, boolean>();
  for (const fn of fnNodes)
    if (fn.name)
      accepted.set(
        fn.name.text,
        !diagnostics.some(
          (d) => d.pos >= fn.getStart(sf) && d.pos < fn.end,
        ),
      );

  return {
    doc: {
      file,
      sourceSha256: ast.sourceSha256,
      types,
      functions,
    },
    omissions,
    ast,
    accepted,
  };
}

/* ---------------------------------------------------------------- main -- */

if (process.argv[1] && import.meta.filename === resolve(process.argv[1])) {
  const [file, ...rest] = process.argv.slice(2);
  let out: string | null = null;
  while (rest.length) {
    const flag = rest.shift();
    const next = rest[0];
    if (flag === "--out" && next !== undefined) { rest.shift(); out = next; }
    else {
      process.stderr.write(`invalid option ${flag}\n`);
      process.exit(1);
    }
  }
  if (!file || !out) {
    process.stderr.write("usage: tsc-claims.mts <file.ts> --out <claims.json>\n");
    process.exit(1);
  }
  try {
    const { doc, omissions, accepted } = produce(file);
    writeFileSync(out + ".outcomes.json", JSON.stringify(Object.fromEntries(accepted)) + "\n");
    writeFileSync(out, JSON.stringify(doc, null, 2) + "\n");
    writeFileSync(out + ".omissions.json", JSON.stringify(omissions, null, 2) + "\n");
    process.stderr.write(
      `${doc.functions.length} function(s) claimed, ${omissions.length} omitted site(s)/reason(s).\n`,
    );
    close();
  } catch (e) {
    process.stderr.write(messageOf(e) + "\n");
    process.exit(1);
  }
}
