#!/usr/bin/env node
/*
 * Trusted front end for the verification experiment (see verification/DESIGN.md).
 *
 * Parses a .ts file with the TypeScript compiler API and emits the abstract
 * syntax tree as JSON, with every node carrying its [start, end) character
 * offsets. Anything outside the fragment is a hard error: this file is also
 * the SYNTACTIC GATE, so a program it rejects can never be certified.
 *
 * This program is TRUSTED. It defines what the source text means; the
 * verifier never sees SKJS's own parse.
 */
"use strict";

const fs = require("fs");
const path = require("path");
const ts = require("typescript");

let sourceFile = null;
const stateful = process.argv.includes("--stateful");

function fail(node, msg) {
  const start = node ? node.getStart(sourceFile) : 0;
  const lc = sourceFile.getLineAndCharacterOfPosition(start);
  throw new Error(`gate: ${msg} (line ${lc.line + 1}, col ${lc.character + 1})`);
}

function span(node) {
  return [node.getStart(sourceFile), node.end];
}

/* ---------------------------------------------------------------- types -- */

// Numeric literals in the fragment are plain decimals; every other spelling (hex, binary,
// octal, separators, bigint) is outside the fragment.
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

function atomsOfTypeNode(node, acc) {
  switch (node.kind) {
    case ts.SyntaxKind.ParenthesizedType:
      return atomsOfTypeNode(node.type, acc);
    case ts.SyntaxKind.UnionType:
      node.types.forEach((t) => atomsOfTypeNode(t, acc));
      return;
    case ts.SyntaxKind.TypeLiteral: {
      if (!stateful || node.members.length !== 1) fail(node, "expected a single cell field");
      const f = node.members[0];
      if (!ts.isPropertySignature(f) || !ts.isIdentifier(f.name) || f.name.text !== "value" ||
          f.questionToken || (f.modifiers && f.modifiers.length)) fail(f, "expected required mutable value field");
      const t = typeOf(f.type);
      acc.push({a: "record", fields: [{name: "value", optional: false, read: t, write: t}],
        indexes: {string: "absent", number: "absent", symbol: "absent"},
        call: "unknown", construct: "unknown", array: "unknown"});
      return;
    }
    case ts.SyntaxKind.StringKeyword:
      acc.push({ a: "string" });
      return;
    case ts.SyntaxKind.NumberKeyword:
      acc.push({ a: "number" });
      return;
    case ts.SyntaxKind.BooleanKeyword:
      acc.push({ a: "boolean" });
      return;
    case ts.SyntaxKind.UndefinedKeyword:
      acc.push({ a: "undefined" });
      return;
    case ts.SyntaxKind.LiteralType: {
      const lit = node.literal;
      if (lit.kind === ts.SyntaxKind.NullKeyword) {
        acc.push({ a: "null" });
        return;
      }
      if (lit.kind === ts.SyntaxKind.StringLiteral) {
        acc.push({ a: "stringlit", v: lit.text });
        return;
      }
      if (lit.kind === ts.SyntaxKind.NumericLiteral) {
        if (!DECIMAL.test(lit.text)) fail(lit, "non-decimal numeric literal type");
        acc.push({ a: "numberlit", v: lit.text });
        return;
      }
      if (lit.kind === ts.SyntaxKind.TrueKeyword) {
        acc.push({ a: "booleanlit", v: "true" });
        return;
      }
      if (lit.kind === ts.SyntaxKind.FalseKeyword) {
        acc.push({ a: "booleanlit", v: "false" });
        return;
      }
      return fail(lit, "literal type outside the fragment");
    }
    default:
      return fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
  }
}

function typeOf(node) {
  if (!node) return fail(node, "missing type annotation");
  const acc = [];
  atomsOfTypeNode(node, acc);
  return { top: false, atoms: acc };
}

/* ---------------------------------------------------------- expressions -- */

function expr(node) {
  switch (node.kind) {
    case ts.SyntaxKind.ParenthesizedExpression:
      // Parentheses carry no meaning of their own, but SKJS records the type
      // of a parenthesised expression at the span of the outermost
      // parenthesis. Unwrap, and widen the span to match, so the two agree on
      // the key. Nested parentheses widen again at each level.
      return { ...expr(node.expression), pos: span(node) };

    case ts.SyntaxKind.Identifier:
      if (node.text === "undefined") {
        return { k: "lit", pos: span(node), lit: { a: "undefined" } };
      }
      return { k: "id", pos: span(node), name: node.text };

    case ts.SyntaxKind.NullKeyword:
      return { k: "lit", pos: span(node), lit: { a: "null" } };
    case ts.SyntaxKind.TrueKeyword:
      return { k: "lit", pos: span(node), lit: { a: "booleanlit", v: "true" } };
    case ts.SyntaxKind.FalseKeyword:
      return { k: "lit", pos: span(node), lit: { a: "booleanlit", v: "false" } };
    case ts.SyntaxKind.StringLiteral:
      // node.text is the DECODED value, which is what a literal type denotes.
      return { k: "lit", pos: span(node), lit: { a: "stringlit", v: node.text } };
    case ts.SyntaxKind.NumericLiteral:
      if (!DECIMAL.test(node.text)) fail(node, "non-decimal numeric literal");
      return { k: "lit", pos: span(node), lit: { a: "numberlit", v: node.text } };

    case ts.SyntaxKind.ObjectLiteralExpression: {
      if (!stateful || node.properties.length !== 1) fail(node, "expected plain single-field allocation");
      const f = node.properties[0];
      if (!ts.isPropertyAssignment(f) || !ts.isIdentifier(f.name) || f.name.text !== "value")
        fail(f, "expected plain value property; no accessors, methods or spreads");
      return {k: "alloc", pos: span(node), e: expr(f.initializer)};
    }
    case ts.SyntaxKind.PropertyAccessExpression:
      if (!stateful || node.questionDotToken || node.name.text !== "value") fail(node, "expected cell.value");
      return {k: "read", pos: span(node), e: expr(node.expression)};
    case ts.SyntaxKind.TypeOfExpression:
      return { k: "typeof", pos: span(node), e: expr(node.expression) };

    case ts.SyntaxKind.PrefixUnaryExpression:
      if (node.operator !== ts.SyntaxKind.ExclamationToken) {
        fail(node, "unary operator outside the fragment");
      }
      return { k: "not", pos: span(node), e: expr(node.operand) };

    case ts.SyntaxKind.BinaryExpression: {
      if (stateful && node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        if (!ts.isPropertyAccessExpression(node.left) || node.left.questionDotToken || node.left.name.text !== "value")
          fail(node.left, "only cell.value assignments are supported");
        return {k: "write", pos: span(node), receiver: expr(node.left.expression), rhs: expr(node.right)};
      }
      const ops = {
        [ts.SyntaxKind.EqualsEqualsEqualsToken]: "===",
        [ts.SyntaxKind.ExclamationEqualsEqualsToken]: "!==",
        [ts.SyntaxKind.AmpersandAmpersandToken]: "&&",
        [ts.SyntaxKind.BarBarToken]: "||",
      };
      const op = ops[node.operatorToken.kind];
      if (!op) fail(node, `binary operator outside the fragment (${node.operatorToken.getText(sourceFile)})`);
      return { k: "bin", pos: span(node), op, l: expr(node.left), r: expr(node.right) };
    }

    case ts.SyntaxKind.CallExpression: {
      if (node.expression.kind !== ts.SyntaxKind.Identifier) {
        fail(node, "only calls to a named top-level function are in the fragment");
      }
      if (node.typeArguments && node.typeArguments.length > 0) {
        fail(node, "explicit type arguments are outside the fragment");
      }
      return {
        k: "call",
        pos: span(node),
        callee: node.expression.text,
        calleePos: span(node.expression),
        args: node.arguments.map(expr),
      };
    }

    default:
      return fail(node, `expression outside the fragment (${ts.SyntaxKind[node.kind]})`);
  }
}

/* ---------------------------------------------------------- statements --- */

function block(node) {
  if (node.kind !== ts.SyntaxKind.Block) fail(node, "expected a block");
  return node.statements.map(stmt);
}

function stmt(node) {
  switch (node.kind) {
    case ts.SyntaxKind.ExpressionStatement:
      if (!stateful) fail(node, "expression statements outside the fragment");
      return {k: "effect", pos: span(node), e: expr(node.expression)};
    case ts.SyntaxKind.ReturnStatement:
      if (!node.expression) fail(node, "a bare `return` is outside the fragment");
      return { k: "return", pos: span(node), e: expr(node.expression) };

    case ts.SyntaxKind.VariableStatement: {
      const dl = node.declarationList;
      if (!(dl.flags & ts.NodeFlags.Const)) fail(node, "only `const` bindings are in the fragment");
      if (dl.declarations.length !== 1) fail(node, "one binding per `const` in the fragment");
      const d = dl.declarations[0];
      if (d.name.kind !== ts.SyntaxKind.Identifier) fail(d, "destructuring is outside the fragment");
      if (!d.initializer) fail(d, "a `const` needs an initializer");
      return {
        k: "const",
        pos: span(node),
        name: d.name.text,
        namePos: span(d.name),
        annot: d.type ? typeOf(d.type) : null,
        init: expr(d.initializer),
      };
    }

    case ts.SyntaxKind.IfStatement:
      if (node.elseStatement && node.elseStatement.kind !== ts.SyntaxKind.Block) {
        fail(node.elseStatement, "`else if` and non-block branches are outside the fragment");
      }
      return {
        k: "if",
        pos: span(node),
        cond: expr(node.expression),
        then: block(node.thenStatement),
        else_: node.elseStatement ? block(node.elseStatement) : null,
      };

    default:
      return fail(node, `statement outside the fragment (${ts.SyntaxKind[node.kind]})`);
  }
}

/* ----------------------------------------------------------- functions --- */

function functionDecl(node) {
  if (!node.name) fail(node, "anonymous function");
  if (node.typeParameters && node.typeParameters.length > 0) {
    fail(node, "generics are outside the fragment");
  }
  if (node.modifiers && node.modifiers.length > 0) {
    fail(node, "modifiers (export/async/declare) are outside the fragment");
  }
  if (!node.body) fail(node, "a function must have a body");
  const params = node.parameters.map((p) => {
    if (p.name.kind !== ts.SyntaxKind.Identifier) fail(p, "destructuring parameter");
    if (p.questionToken) fail(p, "optional parameters are outside the fragment");
    if (p.dotDotDotToken) fail(p, "rest parameters are outside the fragment");
    if (p.initializer) fail(p, "default parameters are outside the fragment");
    return { name: p.name.text, pos: span(p.name), type: typeOf(p.type) };
  });
  return {
    name: node.name.text,
    namePos: span(node.name),
    params,
    retType: typeOf(node.type),
    body: block(node.body),
  };
}

/* ---------------------------------------------------------------- main --- */

function main() {
  const file = process.argv[2];
  if (!file) {
    process.stderr.write("usage: parse-source.js <file.ts> [--stateful]\n");
    process.exit(2);
  }
  const text = fs.readFileSync(file, "utf8");
  sourceFile = ts.createSourceFile(
    path.basename(file),
    text,
    ts.ScriptTarget.ES2020,
    true,
  );
  // A syntax error in the trusted parse is a gate rejection, not a warning.
  const diags = sourceFile.parseDiagnostics || [];
  if (diags.length > 0) {
    throw new Error(`gate: parse error: ${ts.flattenDiagnosticMessageText(diags[0].messageText, " ")}`);
  }
  const functions = sourceFile.statements.map((s) => {
    if (s.kind !== ts.SyntaxKind.FunctionDeclaration) {
      fail(s, `top-level statement outside the fragment (${ts.SyntaxKind[s.kind]})`);
    }
    return functionDecl(s);
  });
  if (functions.length === 0) fail(null, "no functions in file");
  process.stdout.write(JSON.stringify({ file, functions }, null, 1));
}

try {
  main();
} catch (e) {
  process.stderr.write(String(e.message || e) + "\n");
  process.exit(1);
}
