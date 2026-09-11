#!/usr/bin/env node
"use strict";
/*
 * A second claims producer for `stateful-source-v3`. Where SKJS's own export
 * (`skjs.sh --emit-skjs-type-claims`) states what SKJS's checker believes at
 * every site of a source fragment file, this states what the TypeScript
 * compiler's own checker believes at the same sites, so the two can be run
 * through the same independent verifier and compared.
 *
 * Sites come from the trusted parser's own AST (parse-source.js), walked with
 * the same rule the verifier uses to decide what is an entry and what is an
 * expression (SourceClaimJson.functionSites / exprSites, in
 * verification/lean/Verification/ExperimentState/SourceClaimJson.lean). A site
 * is matched to a real TypeScript node by exact [start,end) span, and its type
 * comes from `checker.getTypeAtLocation`. A type this tool cannot state as a
 * calculus label is omitted, never guessed: the omission, with the reason and
 * `checker.typeToString`'s rendering, goes to `<out>.omissions.json`, and the
 * whole function is left out of the claims document, since one missing site
 * would fail extraction anyway.
 */
const fs = require("fs");
const ts = require("typescript");
const { parseFile } = require("./parse-source.js");

/* -------------------------------------------------------------- refusal -- */

class Refusal extends Error {
  constructor(reason, tsType) {
    super(reason);
    this.reason = reason;
    this.tsType = tsType;
  }
}

/* ------------------------------------------------------ sites, from AST -- */
// Mirrors SourceClaimJson.functionSites/exprSites/stmtSites exactly, over the
// JSON parse-source.js emits (the same node shapes SourceInput.decodeExpr and
// decodeStmt decode). An entry is a statement or lowered-closure-body node's
// own start; an expression is a full-span claim. A node kind neither module
// accepts is outside the lowered fragment, so the whole function is unusable
// here regardless of what its types would translate to.

function addEntry(out, pos) {
  out.entries.add(pos[0]);
}
function addExpr(out, pos, kind) {
  const key = pos[0] + ":" + pos[1];
  if (!out.exprs.has(key)) out.exprs.set(key, { pos, kind });
}

function walkExpr(e, out) {
  switch (e.k) {
    case "id":
    case "lit":
      addExpr(out, e.pos, e.k);
      return;
    case "not":
    case "alloc":
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
    case "apply":
      addExpr(out, e.pos, "apply");
      walkExpr(e.callee, out);
      walkExpr(e.arg, out);
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
      addEntry(out, e.pos);
      walkExpr(e.cond, out);
      walkExpr(e.then, out);
      walkExpr(e.else_, out);
      return;
    case "seqBody":
    case "letBody":
      addEntry(out, e.pos);
      walkExpr(e.init, out);
      walkExpr(e.body, out);
      return;
    case "returnBody":
      addEntry(out, e.pos);
      walkExpr(e.e, out);
      return;
    case "doneBody":
      // Administrative completion; no source expression claim.
      return;
    default:
      throw new Error(`expression outside the lowered fragment (${e.k})`);
  }
}

function walkStmt(s, out) {
  switch (s.k) {
    case "break":
    case "continue":
      addEntry(out, s.pos);
      return;
    case "return":
      addEntry(out, s.pos);
      walkExpr(s.e, out);
      return;
    case "const":
      addEntry(out, s.pos);
      walkExpr(s.init, out);
      return;
    case "effect":
      addEntry(out, s.pos);
      walkExpr(s.e, out);
      return;
    case "while":
      // The loop head: the invariant candidate checked on entry and every
      // back edge.
      addEntry(out, s.pos);
      walkExpr(s.cond, out);
      s.body.forEach((st) => walkStmt(st, out));
      return;
    case "if":
      addEntry(out, s.pos);
      walkExpr(s.cond, out);
      s.then.forEach((st) => walkStmt(st, out));
      (s.else_ || []).forEach((st) => walkStmt(st, out));
      return;
    default:
      throw new Error(`statement outside the lowered fragment (${s.k})`);
  }
}

function functionSites(fnJson) {
  const out = { entries: new Set(), exprs: new Map() };
  fnJson.body.forEach((st) => walkStmt(st, out));
  return out;
}

/* ------------------------------------------------------- real AST index -- */
// A site's span, taken from the trusted parser's own output, is matched to
// the TypeScript node with that same [getStart(sf), end) span: the checker
// speaks about nodes, the parser speaks about offsets, and this is the one
// place the two vocabularies meet.

const STATEMENT_KINDS = new Set([
  ts.SyntaxKind.ReturnStatement,
  ts.SyntaxKind.VariableStatement,
  ts.SyntaxKind.IfStatement,
  ts.SyntaxKind.WhileStatement,
  ts.SyntaxKind.BreakStatement,
  ts.SyntaxKind.ContinueStatement,
  ts.SyntaxKind.ExpressionStatement,
]);

function buildIndices(sf) {
  const stmtByStart = new Map();
  const exprBySpan = new Map();
  (function visit(node) {
    const start = node.getStart(sf);
    if (STATEMENT_KINDS.has(node.kind) && !stmtByStart.has(start)) {
      stmtByStart.set(start, node);
    }
    exprBySpan.set(start + ":" + node.end, node);
    ts.forEachChild(node, visit);
  })(sf);
  return { stmtByStart, exprBySpan };
}

/* --------------------------------------------------- type -> labels --- */
// The document's own type table: the four primitives, then one row per
// compound type on first use (SOURCE-CLAIMS.md). Rows are interned by exact
// content, so equal types always share a label.

function dedupSortInts(xs) {
  return Array.from(new Set(xs)).sort((a, b) => a - b);
}
function arrCompare(a, b) {
  const n = Math.max(a.length, b.length);
  for (let i = 0; i < n; i++) {
    const x = a[i] === undefined ? -Infinity : a[i];
    const y = b[i] === undefined ? -Infinity : b[i];
    if (x !== y) return x - y;
  }
  return 0;
}
function dedupSortArrays(arrs) {
  const sorted = arrs.map((a) => a.slice()).sort(arrCompare);
  const out = [];
  for (const a of sorted)
    if (!out.length || arrCompare(out[out.length - 1], a) !== 0) out.push(a);
  return out;
}
function internRow(types, row) {
  const key = JSON.stringify(row);
  for (let i = 0; i < types.length; i++)
    if (JSON.stringify(types[i]) === key) return i;
  types.push(row);
  return types.length - 1;
}

// A type built only from null/true/false/undefined/boolean/never, as a
// sorted, duplicate-free list of primitive labels, or null if the type (or
// some union member) is none of those.
function primitiveLabelsOf(type) {
  const f = type.flags;
  if (f & ts.TypeFlags.Null) return [0];
  if (f & ts.TypeFlags.Undefined) return [3];
  if (f & ts.TypeFlags.Never) return [];
  if (f & ts.TypeFlags.Boolean) return [1, 2]; // the `boolean` pseudo-union itself
  if (f & ts.TypeFlags.BooleanLiteral)
    return type.intrinsicName === "true" ? [1] : [2];
  if (type.isUnion()) {
    const acc = [];
    for (const t of type.types) {
      const sub = primitiveLabelsOf(t);
      if (sub === null) return null;
      acc.push(...sub);
    }
    return dedupSortInts(acc);
  }
  return null;
}
function primitiveOnly(type, checker) {
  const p = primitiveLabelsOf(type);
  if (p === null)
    throw new Refusal("nested-non-primitive", checker.typeToString(type));
  return p;
}

// `{ value: T }`-shaped: exactly one required, non-readonly property named
// "value", no index signatures, and not itself callable. `ok:false` with no
// reason means "not object-shaped at all, try the arrow reading instead";
// with a reason it means "object-shaped but not this exact contract".
function tryRecord(type, checker) {
  if (!(type.flags & ts.TypeFlags.Object)) return { ok: false };
  if (
    checker.getSignaturesOfType(type, ts.SignatureKind.Call).length ||
    checker.getSignaturesOfType(type, ts.SignatureKind.Construct).length
  ) {
    return { ok: false };
  }
  const props = type.getProperties();
  if (props.length !== 1)
    return {
      ok: false,
      reason: props.length === 0 ? "no-value-field" : "several-properties",
    };
  const prop = props[0];
  if (prop.getName() !== "value")
    return { ok: false, reason: "no-value-field" };
  if (checker.getIndexInfosOfType(type).length)
    return { ok: false, reason: "indexed-type" };
  if (prop.flags & ts.SymbolFlags.Optional)
    return { ok: false, reason: "optional-field" };
  const decl =
    prop.valueDeclaration || (prop.declarations && prop.declarations[0]);
  if (decl && ts.getCombinedModifierFlags(decl) & ts.ModifierFlags.Readonly) {
    return { ok: false, reason: "readonly-field" };
  }
  return { ok: true, valueType: checker.getTypeOfSymbol(prop) };
}

// `(x: D) => R`-shaped: one signature, one required ordinary parameter, no
// type parameters, no `this` parameter.
function tryArrow(type, checker) {
  const sigs = checker.getSignaturesOfType(type, ts.SignatureKind.Call);
  if (sigs.length === 0) return { ok: false };
  if (
    sigs.length !== 1 ||
    checker.getSignaturesOfType(type, ts.SignatureKind.Construct).length
  ) {
    return { ok: false, reason: "overloaded-arrow" };
  }
  const sig = sigs[0];
  if (sig.typeParameters && sig.typeParameters.length)
    return { ok: false, reason: "generic-arrow" };
  if (sig.thisParameter) return { ok: false, reason: "this-param" };
  if (sig.parameters.length !== 1) {
    return {
      ok: false,
      reason:
        sig.parameters.length === 0
          ? "no-parameter-arrow"
          : "multi-param-arrow",
    };
  }
  const p = sig.parameters[0];
  const decl = p.valueDeclaration;
  if (decl && decl.questionToken)
    return { ok: false, reason: "optional-param" };
  if (decl && decl.dotDotDotToken) return { ok: false, reason: "rest-param" };
  return {
    ok: true,
    domain: checker.getTypeOfSymbol(p),
    result: sig.getReturnType(),
  };
}

function basicReason(type) {
  const f = type.flags;
  if (f & ts.TypeFlags.Void) return "void";
  if (f & (ts.TypeFlags.String | ts.TypeFlags.StringLiteral)) return "string";
  if (f & (ts.TypeFlags.Number | ts.TypeFlags.NumberLiteral)) return "number";
  if (f & ts.TypeFlags.Any) return "any";
  if (f & ts.TypeFlags.Unknown) return "unknown";
  if (f & ts.TypeFlags.TypeParameter) return "generic";
  if (f & ts.TypeFlags.Object) return "object-shape";
  return "unsupported-type";
}

// An intersection of record contracts, as {first, rest} (both sorted,
// duplicate-free label lists) — or null if the operands are not all records,
// which leaves an arrow intersection still to try.
function tryRecordIntersection(type, checker) {
  const results = type.types.map((t) => tryRecord(t, checker));
  if (!results.every((r) => r.ok)) {
    const bad = results.find((r) => !r.ok && r.reason);
    if (bad) throw new Refusal(bad.reason, checker.typeToString(type));
    return null;
  }
  const operands = dedupSortArrays(
    results.map((r) => primitiveOnly(r.valueType, checker)),
  );
  return operands.length === 1
    ? { first: operands[0], rest: [] }
    : { first: operands[0], rest: operands.slice(1) };
}

// An intersection of arrow signatures, as a declaration-order, repeat-free
// list of [D, R] pairs — or null if the operands are not all arrows.
function tryArrowIntersection(type, checker) {
  const results = type.types.map((t) => tryArrow(t, checker));
  if (!results.every((r) => r.ok)) {
    const bad = results.find((r) => !r.ok && r.reason);
    if (bad) throw new Refusal(bad.reason, checker.typeToString(type));
    return null;
  }
  const arrows = [];
  for (const r of results) {
    const pair = [
      primitiveOnly(r.domain, checker),
      primitiveOnly(r.result, checker),
    ];
    if (!arrows.some((a) => JSON.stringify(a) === JSON.stringify(pair)))
      arrows.push(pair);
  }
  return arrows;
}

function translateType(type, checker, types) {
  const prim = primitiveLabelsOf(type);
  if (prim !== null) return prim;
  if (type.isIntersection()) {
    const refs = tryRecordIntersection(type, checker);
    if (refs) return [internRow(types, [{ refs }])];
    const arrows = tryArrowIntersection(type, checker);
    if (arrows) return [internRow(types, [{ arrs: { arrows } }])];
    throw new Refusal("mixed-intersection", checker.typeToString(type));
  }
  // A union is a label list, and the format admits one mixing cell and arrow
  // atoms with primitives, so each member contributes its own labels.
  if (type.isUnion()) {
    const labels = [];
    for (const member of type.types)
      labels.push(...translateType(member, checker, types));
    return dedupSortInts(labels);
  }
  const rec = tryRecord(type, checker);
  if (rec.ok)
    return [
      internRow(types, [
        { refs: { first: primitiveOnly(rec.valueType, checker), rest: [] } },
      ]),
    ];
  if (rec.reason) throw new Refusal(rec.reason, checker.typeToString(type));
  const arr = tryArrow(type, checker);
  if (arr.ok) {
    const pair = [
      primitiveOnly(arr.domain, checker),
      primitiveOnly(arr.result, checker),
    ];
    return [internRow(types, [{ arrs: { arrows: [pair] } }])];
  }
  if (arr.reason) throw new Refusal(arr.reason, checker.typeToString(type));
  throw new Refusal(basicReason(type), checker.typeToString(type));
}

// Object literals and arrow functions are contextually typed: TypeScript's
// own type for the node is the narrowest branch it can infer on its own
// (e.g. one record or one signature), but a claim allocating into or
// implementing a conjoined contract needs the wider annotation the value is
// held to, exactly as source-claims.js's handwritten fixture for
// arrow-intersection.ts does. Prefer that contextual type when it exists and
// translates; the node's own type is always the sound fallback.
//
// A `.value` read is a different case: TypeScript narrows a property access
// across a straight-line write (`cell.value = false; ...cell.value...` reads
// as `false`), but the calculus reads a cell at its declared invariant unless
// the point carries an explicit current-content assertion, which this
// producer never writes. Claiming the narrower TypeScript type here states
// something the calculus does not (and need not) grant, so a read's claim is
// always the cell's own invariant: the `first` contract of whatever row its
// receiver's own type interns.
function readInvariant(node, checker, types) {
  const cellType = checker.getTypeAtLocation(node.expression);
  const cellLabels = translateType(cellType, checker, types);
  if (cellLabels.length === 1) {
    const row = types[cellLabels[0]];
    const clause = Array.isArray(row) && row.length === 1 ? row[0] : null;
    if (clause && clause.refs) return clause.refs.first;
  }
  throw new Refusal("read-of-non-reference", checker.typeToString(cellType));
}

// TypeScript folds a boolean local declared with a wider annotation but a
// literal initializer (`const condition: boolean = true;`) back to that
// literal, and then marks whichever arm of `if (condition)` the literal
// rules out as unreachable — every reference there reads back as `never`.
// The calculus does not fold constants across a test: `if`/`while` on a bare
// name or its negation (`conditionVariable`, SourceExtraction.lean) narrows
// the tested binding to `true`/`false` in the corresponding arm regardless of
// its initializer, and both arms stay live. So `never` on a reference to a
// local is never trusted outright — it is TypeScript proving more than the
// calculus's model of this one test does, not a fact the calculus can use.
function testedIdentitySymbol(cond, checker) {
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
// Walks outward from a reference through enclosing `if`/`while` statements,
// applying the innermost one that tests this same binding by bare identity.
function truthyGuardLabels(node, checker) {
  const sym = checker.getSymbolAtLocation(node);
  if (!sym) return null;
  let child = node;
  let cur = node.parent;
  while (cur && !ts.isFunctionLike(cur)) {
    if (ts.isIfStatement(cur) || ts.isWhileStatement(cur)) {
      const tested = testedIdentitySymbol(cur.expression, checker);
      if (tested && tested.sym === sym) {
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
// The general fallback once `never` is rejected: the binding's own declared
// type, ignoring flow entirely. Always sound, since it is what every value
// the binding could ever hold is required to satisfy.
function declaredTypeAt(node, checker, types) {
  const sym = checker.getSymbolAtLocation(node);
  if (sym) return translateType(checker.getTypeOfSymbol(sym), checker, types);
  throw new Refusal("unreachable-per-typescript", "never");
}
// The one place every reference to a local binding is priced: a real guard
// wins outright (it is what the calculus itself would derive); failing that,
// a binding already known to disagree with TypeScript about its own value
// (`authoritativeType`) uses that fixed reading instead of asking flow at
// all; only a plain, untainted local defers to TypeScript's own answer, with
// `never` still rejected in favor of the declared type since it is always
// TypeScript proving a stronger fact than a test the calculus has no rule
// for is entitled to.
function bestLabelsForReference(node, checker, types, declCache) {
  const guard = truthyGuardLabels(node, checker);
  if (guard) return guard;
  if (declCache) {
    const sym = checker.getSymbolAtLocation(node);
    const decl =
      sym &&
      (sym.valueDeclaration || (sym.declarations && sym.declarations[0]));
    if (
      decl &&
      decl.getSourceFile() === node.getSourceFile() &&
      (ts.isVariableDeclaration(decl) || ts.isParameter(decl))
    ) {
      const auth = authoritativeType(
        { decl, name: node.text, sym },
        checker,
        types,
        declCache,
      );
      // A tainted binding (read- or literal-tainted; see `authoritativeType`)
      // is wrong everywhere but a matching guard: the calculus's own
      // internal value for it is its fixed reading (a read's cell invariant,
      // or a `const`'s declared annotation — the cast a `const` compiles to,
      // never the narrower literal TypeScript tracks for it), so a claim
      // anywhere has to be provable from that, not from whatever TypeScript
      // additionally happens to know. A matching guard is the one exception,
      // already returned above — the one place the compiled program itself
      // narrows the binding's own internal value, exactly enough to justify
      // the arm's tighter claim.
      if (
        auth.readTainted ||
        (auth.declared &&
          JSON.stringify(auth.declared) !== JSON.stringify(auth.claimed))
      ) {
        return auth.labels;
      }
    }
  }
  const t = checker.getTypeAtLocation(node);
  if (t.flags & ts.TypeFlags.Never) return declaredTypeAt(node, checker, types);
  return translateType(t, checker, types);
}

// Mirrors the JSON `k` tags parse-source.js assigns, over a real ts.Node, for
// the one place a real node needs re-classifying: a write's own value (see
// below).
function tsExprKind(node) {
  if (ts.isParenthesizedExpression(node)) return tsExprKind(node.expression);
  if (ts.isIdentifier(node)) return "id";
  if (
    node.kind === ts.SyntaxKind.NullKeyword ||
    node.kind === ts.SyntaxKind.TrueKeyword ||
    node.kind === ts.SyntaxKind.FalseKeyword
  ) {
    return "lit";
  }
  if (ts.isPropertyAccessExpression(node)) return "read";
  if (ts.isObjectLiteralExpression(node)) return "alloc";
  if (ts.isArrowFunction(node)) return "lambda";
  if (
    ts.isBinaryExpression(node) &&
    node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
    ts.isPropertyAccessExpression(node.left)
  ) {
    return "write";
  }
  return "other";
}

function typeForExprSite(kind, node, checker, types, declCache) {
  if (kind === "read") return readInvariant(node, checker, types);
  if (kind === "id")
    return bestLabelsForReference(node, checker, types, declCache);
  // JavaScript's assignment expression evaluates to the assigned value, and
  // the calculus's write operation carries that same value forward as the
  // expression's result (SourceExtraction.lean's `.write` case derives the
  // write node's type from the right-hand side's own claim, not from asking
  // separately what the assignment itself evaluates to) — so the write's
  // claim has to be exactly the right-hand side's claim, not a second,
  // independently-asked opinion that could disagree with it.
  if (kind === "write") {
    let assignment = node;
    while (ts.isParenthesizedExpression(assignment))
      assignment = assignment.expression;
    const rhs = assignment.right;
    return typeForExprSite(tsExprKind(rhs), rhs, checker, types, declCache);
  }
  if (kind === "alloc" || kind === "lambda") {
    const ctx = checker.getContextualType(node);
    if (ctx) {
      try {
        return translateType(ctx, checker, types);
      } catch (e) {
        /* fall through to the node's own type */
      }
    }
  }
  return translateType(checker.getTypeAtLocation(node), checker, types);
}

/* ------------------------------------------------- entry environments -- */
// The environment at an entry is every parameter and enclosing-block const
// declared before it (SOURCE-CLAIMS.md), independent of control flow;
// `getSymbolsInScope` gives exactly the lexically visible bindings, filtered
// to this file's own parameters and `const`s declared strictly before the
// site (later same-block bindings are visible in scope tables that do not
// model temporal-dead-zone ordering, so that ordering is enforced here).

function envAtEntry(anchorNode, offset, checker, sf) {
  const symbols = checker.getSymbolsInScope(
    anchorNode,
    ts.SymbolFlags.Variable,
  );
  const seen = [];
  for (const sym of symbols) {
    const decl =
      sym.valueDeclaration || (sym.declarations && sym.declarations[0]);
    if (!decl || decl.getSourceFile() !== sf) continue;
    if (!(ts.isParameter(decl) || ts.isVariableDeclaration(decl))) continue;
    const declStart = decl.name.getStart(sf);
    if (declStart >= offset) continue;
    seen.push({ sym, decl, declStart, name: sym.getName() });
  }
  seen.sort((a, b) => a.declStart - b.declStart);
  return seen;
}

// The real expression, if any, whose flow this entry's own statement is
// keyed on: the condition for `if`/`while`, the initializer for `const`, the
// statement's own expression otherwise. Restricting the search to this
// expression (rather than the whole statement, which for `if`/`while` would
// reach into branches decided *after* this point) keeps the anchor at the
// right point in the control-flow graph.
function anchorSearchScope(stmtNode) {
  if (ts.isIfStatement(stmtNode) || ts.isWhileStatement(stmtNode))
    return stmtNode.expression;
  if (ts.isReturnStatement(stmtNode)) return stmtNode.expression || null;
  if (ts.isVariableStatement(stmtNode))
    return stmtNode.declarationList.declarations[0].initializer;
  if (ts.isExpressionStatement(stmtNode)) return stmtNode.expression;
  return null; // break/continue: no expression to anchor on
}

function isNamePosition(id) {
  const p = id.parent;
  if (!p) return false;
  if (
    (ts.isPropertyAccessExpression(p) ||
      ts.isPropertySignature(p) ||
      ts.isPropertyAssignment(p) ||
      ts.isParameter(p) ||
      ts.isVariableDeclaration(p) ||
      ts.isBindingElement(p)) &&
    p.name === id
  ) {
    return true;
  }
  return false;
}
function findNameRef(scope, name, sf) {
  if (!scope) return null;
  let found = null;
  (function visit(node) {
    if (found) return;
    if (ts.isIdentifier(node) && node.text === name && !isNamePosition(node)) {
      found = node;
      return;
    }
    ts.forEachChild(node, visit);
  })(scope);
  return found;
}

// `getTypeOfSymbolAtLocation` only narrows when its `location` is itself a
// reference resolving to that symbol (checked empirically against
// typescript's own implementation); given any other node it falls back to
// the symbol's plain declared type. So: when the entry's own anchoring
// expression happens to mention this binding, use that reference directly
// (TypeScript narrows it like any other identifier); otherwise fall back to
// the declared type, which is always sound, if not always precise enough for
// the verifier's proof search.
//
// A `const` initialized from a `.value` read is a further trap: TypeScript
// tracks such a binding's value through the read, and a later reference can
// come back narrower than boolean (down to the exact literal last written to
// the cell) even though nothing here reassigns it. That is a true fact about
// this one, alias-free run, but the calculus does not grant it without a
// current-content assertion, which this producer never writes — and it is
// already claiming the read itself at the cell's declared invariant
// (`readInvariant`), so trusting a narrower flow type for the same value
// elsewhere would claim two disagreeing things about it. So a binding is
// "authoritative" at the type its own initializer already claims (matching
// `readInvariant`/the contextual preference used for `alloc`/`lambda`) when
// that differs from TypeScript's own unnarrowed type for it; an authoritative
// binding always uses that fixed type, never a later flow lookup. A
// parameter is never authoritative — it names no initializer to disagree
// with — and neither is a plain `const` TypeScript does not narrow past its
// own declaration.
function declarationExprKind(node) {
  if (ts.isParenthesizedExpression(node))
    return declarationExprKind(node.expression);
  if (ts.isPropertyAccessExpression(node)) return "read";
  if (ts.isObjectLiteralExpression(node)) return "alloc";
  if (ts.isArrowFunction(node)) return "lambda";
  return "other";
}
// A binding disagrees with TypeScript's later narrowing in two distinct ways
// this producer has found by testing against the corpus: a `.value` read
// tracks the cell's exact last-written content past the point the calculus
// grants that without a current-content assertion (never written here), and
// a `const` whose annotation is wider than its initializer's own literal
// type lets TypeScript fold the literal through every later use — including
// treating whichever arm of a subsequent test the literal rules out as
// unreachable (`never`), where the calculus's plain two-armed test
// (`conditionVariable`) keeps both arms live. Either way the binding's own
// declared annotation (or, lacking one, the initializer's own claimed type)
// is what every value it could hold is required to satisfy, so it is always
// a sound ceiling to fall back to. A binding copied one hop from a tainted
// one (`const b = a;`) is not detected here; see the report.
function authoritativeType(binding, checker, types, cache) {
  if (cache.has(binding.decl)) return cache.get(binding.decl);
  let result;
  if (ts.isParameter(binding.decl)) {
    result = {
      labels: null,
      readTainted: false,
      declared: null,
      claimed: null,
    };
  } else {
    const init = binding.decl.initializer;
    const kind = declarationExprKind(init);
    const claimed = typeForExprSite(kind, init, checker, types, cache);
    let declared = null;
    if (binding.decl.type) {
      try {
        declared = translateType(
          checker.getTypeFromTypeNode(binding.decl.type),
          checker,
          types,
        );
      } catch (e) {
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
  cache.set(binding.decl, result);
  return result;
}
// An entry's own anchoring statement rarely mentions every visible binding;
// absent a reference to narrow from, `getTypeOfSymbolAtLocation` with a
// non-matching location already answers with the plain declared type
// (verified empirically against typescript's own implementation) — sound
// regardless of either taint, so nothing further to substitute here.
function bindingLabelsAtEntry(stmtNode, binding, checker, sf, types, cache) {
  const ref = findNameRef(anchorSearchScope(stmtNode), binding.name, sf);
  if (ref) return bestLabelsForReference(ref, checker, types, cache);
  return translateType(
    checker.getTypeOfSymbolAtLocation(binding.sym, stmtNode),
    checker,
    types,
  );
}

/* ------------------------------------------------------------- driver -- */

function omissionRecord(fn, site, err) {
  return {
    function: fn,
    site,
    tsType: err instanceof Refusal ? err.tsType : "",
    reason:
      err instanceof Refusal ? err.reason : String((err && err.message) || err),
  };
}

function processFunction(
  fnJson,
  fnNode,
  checker,
  sf,
  types,
  indices,
  omissions,
) {
  const before = omissions.length;
  const name = fnJson.name;
  const params = fnNode.parameters.map((p) => {
    try {
      return {
        name: p.name.getText(sf),
        type: translateType(checker.getTypeAtLocation(p.name), checker, types),
        current: null,
      };
    } catch (e) {
      omissions.push(
        omissionRecord(name, { kind: "param", name: p.name.getText(sf) }, e),
      );
      return null;
    }
  });
  let result = null;
  try {
    const sig = checker.getSignatureFromDeclaration(fnNode);
    result = translateType(sig.getReturnType(), checker, types);
  } catch (e) {
    omissions.push(omissionRecord(name, { kind: "result" }, e));
  }

  const sites = functionSites(fnJson); // may throw; caller catches per-function
  const declCache = new Map(); // one function's worth of authoritative-binding memo

  const entries = [];
  for (const start of Array.from(sites.entries).sort((a, b) => a - b)) {
    const stmtNode = indices.stmtByStart.get(start);
    if (!stmtNode) {
      omissions.push(
        omissionRecord(
          name,
          { kind: "entry", start },
          new Refusal("site-not-found", ""),
        ),
      );
      continue;
    }
    const bindings = [];
    for (const b of envAtEntry(stmtNode, start, checker, sf)) {
      try {
        const type = bindingLabelsAtEntry(
          stmtNode,
          b,
          checker,
          sf,
          types,
          declCache,
        );
        bindings.push({ name: b.name, type, current: null });
      } catch (e) {
        omissions.push(
          omissionRecord(name, { kind: "entry", start, name: b.name }, e),
        );
      }
    }
    entries.push({ start, bindings });
  }

  const expressions = [];
  for (const [key, { pos, kind }] of Array.from(sites.exprs.entries()).sort(
    (a, b) => a[1].pos[0] - b[1].pos[0],
  )) {
    const node = indices.exprBySpan.get(key);
    if (!node) {
      omissions.push(
        omissionRecord(
          name,
          { kind: "expr", pos },
          new Refusal("site-not-found", ""),
        ),
      );
      continue;
    }
    try {
      expressions.push({
        pos,
        type: typeForExprSite(kind, node, checker, types, declCache),
        current: null,
      });
    } catch (e) {
      omissions.push(omissionRecord(name, { kind: "expr", pos }, e));
    }
  }

  if (omissions.length > before) return null; // one unclaimable site omits the whole function
  return {
    name,
    namePos: fnJson.namePos,
    params,
    result,
    entries,
    expressions,
  };
}

function compilerOptions() {
  // Matches the syntactic gate's target (parse-source.js uses ES2020); strict
  // so nullability and literal types are exactly what the fragment expects.
  return {
    strict: true,
    target: ts.ScriptTarget.ES2020,
    skipLibCheck: true,
    noEmit: true,
  };
}

// Loading the checker costs more than reading any one of these files, so a
// caller with several files builds one program over all of them and passes it
// in. `programOver` is that program; without one, this file gets its own.
function programOver(files) {
  return ts.createProgram(files, compilerOptions());
}

function produce(file, program = programOver([file])) {
  const ast = parseFile(file); // the trusted parse; also the syntactic gate
  const checker = program.getTypeChecker();
  const sf = program.getSourceFile(file);
  if (!sf) throw new Error(`typescript did not load ${file}`);
  const indices = buildIndices(sf);
  const fnNodes = sf.statements.filter((s) => ts.isFunctionDeclaration(s));
  if (fnNodes.length !== ast.functions.length) {
    throw new Error(
      "function count mismatch between the trusted parse and the checker's program",
    );
  }

  const types = [
    ["nul"],
    [{ boolLit: { value: true } }],
    [{ boolLit: { value: false } }],
    ["undef"],
  ];
  const omissions = [];
  const functions = [];
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
      else types.length = before; // discard rows only this abandoned function added
    } catch (e) {
      types.length = before;
      omissions.push(omissionRecord(fnJson.name, { kind: "function" }, e));
    }
  });

  const doc = {
    version: 3,
    profile: "stateful-source-v3",
    file,
    sourceSha256: ast.sourceSha256,
    types,
    functions,
  };
  // The checker's own verdict, from the program that just typed this file:
  // what `tsc --noEmit` would say, without a second run. A diagnostic belongs
  // to the function whose span contains it, so one bad function does not
  // speak for the rest of the file.
  const diagnostics = [
    ...program.getSyntacticDiagnostics(sf),
    ...program.getSemanticDiagnostics(sf),
  ];
  const accepted = new Map();
  for (const fn of fnNodes)
    if (fn.name)
      accepted.set(
        fn.name.text,
        !diagnostics.some(
          (d) =>
            d.start !== undefined &&
            d.start >= fn.getStart(sf) &&
            d.start < fn.end,
        ),
      );
  return { doc, omissions, ast, accepted };
}

function main(argv) {
  const file = argv[0];
  const rest = argv.slice(1);
  let out = null;
  while (rest.length) {
    const k = rest.shift();
    if (k === "--out" && rest.length) out = rest.shift();
    else throw new Error(`invalid option ${k}`);
  }
  if (!file || !out)
    throw new Error("usage: tsc-claims.js <file.ts> --out <claims.json>");
  const { doc, omissions } = produce(file);
  fs.writeFileSync(out, JSON.stringify(doc, null, 2) + "\n");
  fs.writeFileSync(
    out + ".omissions.json",
    JSON.stringify(omissions, null, 2) + "\n",
  );
  process.stderr.write(
    `${doc.functions.length} function(s) claimed, ${omissions.length} omitted site(s)/reason(s).\n`,
  );
}

if (require.main === module) {
  try {
    main(process.argv.slice(2));
  } catch (e) {
    process.stderr.write(String(e.message || e) + "\n");
    process.exit(1);
  }
} else {
  module.exports = {
    produce,
    programOver,
    functionSites,
    translateType,
    primitiveLabelsOf,
  };
}
