#!/usr/bin/env node
/*
 * Trusted front end for the verification experiment (see verification/DESIGN.md).
 *
 * Reads a .ts file and emits a tree of the fragment language (fragment.mts) as
 * JSON, with every node carrying its [start, end) offsets in UTF-16 code units.
 * This program is the SYNTACTIC GATE: a construct outside the fragment is an
 * error, so a program it rejects can never be certified. Anything it accepts,
 * it describes exactly.
 *
 * This program is TRUSTED. It defines what the source text means; the verifier
 * never sees the producer's own parse. The fragment it accepts is stated in
 * ../AGENTS.md and, as a grammar, in the pull request description.
 */
import { API } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type {
  ArrowFunction,
  BinaryExpression,
  Expression,
  FunctionDeclaration,
  Node,
  SourceFile,
  Statement,
  TypeAliasDeclaration,
  VariableStatement,
  TypeNode,
} from "typescript/unstable/ast";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import type { ClaimType, Atom } from "./claim.mts";
import type {
  Ast,
  BindingAst,
  Expr,
  FunctionAst,
  PatternPropAst,
  Stmt,
  TypeAliasAst,
  TypeParamAst,
  ArithOp,
} from "./fragment.mts";
import type { Span } from "./span.mts";
import { messageOf } from "./thrown.mts";

/* --------------------------------------------------------- the compiler -- */
// The compiler runs out of process and is addressed through one API instance.
// Opening it costs more than reading any one file, so a process that parses
// several shares it, and a process that parses one still pays it once.

let compiler: API | null = null;

// The text this process is working with, per absolute path. The compiler runs
// in another process with its own view of the disk, and a tool that holds a
// source in memory — an annotated rendering, a candidate edit, a fixture it
// just wrote — needs the tree to be the tree of *that* text, not of whatever
// the disk happens to hold. An entry here is what the compiler reads; a path
// with no entry falls through to the real file.
const contents = new Map<string, string>();
const opened = new Set<string>();

/**
 * The project that owns a file: whichever `tsconfig.json` above it claims it,
 * or an inferred one. Exported because a checker-side consumer of this parse
 * needs the same project (and the same compiler process) the gate used.
 */
export function projectFor(absolute: string) {
  compiler ??= new API({
    cwd: dirname(absolute),
    fs: {
      readFile: (name) => contents.get(name),
      fileExists: (name) => (contents.has(name) ? true : undefined),
    },
  });
  // A file the compiler already holds is re-read rather than reused: the text
  // for a path can change between two opens in one process, and reusing the
  // first tree would leave every span pointing into a file that is no longer
  // there.
  const snapshot = compiler.updateSnapshot({
    openFiles: [absolute],
    ...(opened.has(absolute) ? { fileChanges: { changed: [absolute] } } : {}),
  });
  opened.add(absolute);
  const project = snapshot.getDefaultProjectForFile(absolute);
  if (!project) throw new Error(`the compiler did not open ${absolute}`);
  return project;
}

/**
 * The compiler's tree for `text`, read as the file at `absolute`. The path
 * decides which `tsconfig.json` governs the file and what a diagnostic names;
 * the text is what is actually parsed.
 */
export function openText(absolute: string, text: string): SourceFile {
  contents.set(absolute, text);
  const file = projectFor(absolute).program.getSourceFile(absolute);
  if (!file) throw new Error(`the compiler produced no tree for ${absolute}`);
  return file;
}

function openFile(absolute: string, text: string): SourceFile {
  contents.set(absolute, text);
  const project = projectFor(absolute);
  const syntax = project.program.getSyntacticDiagnostics(absolute);
  if (syntax.length > 0)
    throw new Error(`gate: parse error: ${syntax[0].text}`);
  const file = project.program.getSourceFile(absolute);
  if (!file)
    throw new Error(`gate: the compiler produced no tree for ${absolute}`);
  return file;
}

/** Release the compiler. A long-lived caller may parse again afterwards. */
export function close(): void {
  compiler?.close();
  compiler = null;
  opened.clear();
  contents.clear();
}

/* -------------------------------------------------------------- the gate -- */
// One parse owns one source file. `fail` and `span` are the only two things
// that need it, and they are the only two that should: a gate rejection names
// a place in the file it is reading.

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators, bigint) is outside it.
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

const NULL_TYPE: ClaimType = { top: false, atoms: [{ a: "null" }] };

class Gate {
  // Written out rather than a parameter property: node strips types, it does
  // not compile them, so the syntax has to be erasable.
  private readonly file: SourceFile;
  private readonly typeParams = new Set<string>();
  private readonly aliasNames = new Set<string>();
  private aliasApps = false;
  constructor(file: SourceFile) {
    this.file = file;
  }

  registerAlias(name: string, node: Node): void {
    if (this.aliasNames.has(name)) this.fail(node, "duplicate type alias");
    this.aliasNames.add(name);
  }

  enableAliasApps(): void {
    this.aliasApps = true;
  }

  fail(node: Node | null, message: string): never {
    const start = node ? node.getStart(this.file) : 0;
    const at = this.file.getLineAndCharacterOfPosition(start);
    throw new Error(
      `gate: ${message} (line ${at.line + 1}, col ${at.character + 1})`,
    );
  }

  span(node: Node): Span {
    return [node.getStart(this.file), node.end];
  }

  text(node: Node): string {
    return this.file.text.slice(node.getStart(this.file), node.end);
  }

  /* ------------------------------------------------------------- types -- */

  atomsOf(node: TypeNode, acc: Atom[]): void {
    // `kind` narrows nothing here: the AST module's TypeNode is one base
    // interface rather than a union, so each shape is recognized by its own
    // predicate, which is what lets the compiler read the fields below.
    if (ts.isParenthesizedTypeNode(node)) return this.atomsOf(node.type, acc);

    if (ts.isUnionTypeNode(node)) {
      for (const t of node.types) this.atomsOf(t, acc);
      return;
    }

    if (ts.isFunctionTypeNode(node)) {
      if (node.typeParameters?.length)
        this.fail(node, "generic function types are outside the fragment");
      for (const p of node.parameters) {
        if (
          !ts.isIdentifier(p.name) ||
          p.name.text === "this" ||
          p.questionToken ||
          p.dotDotDotToken ||
          p.initializer
        )
          this.fail(p, "expected a required ordinary parameter");
      }
      acc.push({
        a: "function",
        params: node.parameters.map((p) => this.typeOf(p.type)),
        result: this.typeOf(node.type),
        construct: "unknown",
        array: "unknown",
      });
      return;
    }

    if (ts.isTypeLiteralNode(node)) {
      if (!node.members.length)
        this.fail(node, "a record with no field has no location");
      const names = new Set<string>();
      const fields = node.members.map((f) => {
        // A `readonly` member is a read capability: its write contract is
        // `never`, and nothing else about the field changes.
        const readonly =
          ts.isPropertySignatureDeclaration(f) &&
          f.modifiers?.every((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true;
        if (
          !ts.isPropertySignatureDeclaration(f) ||
          !ts.isIdentifier(f.name) ||
          // A member's `?` (or `!`) is its postfix token; a parameter's is a
          // question token. Different nodes, different names.
          f.postfixToken ||
          (f.modifiers?.length && !readonly)
        )
          this.fail(f, "expected a required mutable field");
        const name =
          ts.isPropertySignatureDeclaration(f) && ts.isIdentifier(f.name)
            ? f.name.text
            : this.fail(f, "expected a required mutable field");
        if (names.has(name)) this.fail(f, "duplicate field name in a record");
        names.add(name);
        const t = this.typeOf(
          ts.isPropertySignatureDeclaration(f) ? f.type : undefined,
        );
        return { name, optional: false, read: t, write: readonly ? { top: false, atoms: [] } : t };
      });
      acc.push({
        a: "record",
        fields,
        indexes: { string: "absent", number: "absent", symbol: "absent" },
        call: "unknown",
        construct: "unknown",
        array: "unknown",
      });
      return;
    }

    if (ts.isIntersectionTypeNode(node)) {
      // Union is the atom list; conjunction lives inside the atom kinds that
      // have one, mirroring the clause language, where only a location under
      // several contracts and a function with several signatures conjoin.
      // Nothing else does, so nothing else may be written here: a format
      // that could say `null & boolean` would say something no clause holds.
      // Conjunction is associative, so a parenthesized intersection inside
      // one contributes its operands to the same flat list.
      const operands: TypeNode[] = [];
      const flatten = (t: TypeNode): void => {
        while (ts.isParenthesizedTypeNode(t)) t = t.type;
        if (ts.isIntersectionTypeNode(t)) t.types.forEach(flatten);
        else operands.push(t);
      };
      flatten(node);
      const parts = operands.map((operand) => {
        const one: Atom[] = [];
        this.atomsOf(operand, one);
        if (one.length !== 1)
          this.fail(operand, "an intersection operand must be a single type");
        return one[0];
      });
      const head = parts[0];
      if (parts.some((p) => p.a !== head.a))
        this.fail(node, "intersection operands must have the same shape");
      if (head.a !== "record" && head.a !== "function")
        this.fail(
          node,
          `intersection of ${head.a} types is outside the fragment`,
        );
      acc.push({ ...head, and: parts.slice(1) });
      return;
    }

    if (ts.isTypeReferenceNode(node)) {
      if (node.typeName.kind !== ts.SyntaxKind.Identifier)
        this.fail(node, "type reference outside the fragment");
      const name = node.typeName.text;
      if (node.typeArguments?.length) {
        if (!this.aliasApps)
          this.fail(
            node,
            "alias applications in alias bodies are outside the fragment",
          );
        if (node.typeArguments.length !== 1)
          this.fail(node, "only one type argument is in the fragment");
        if (!this.aliasNames.has(name))
          this.fail(node, "unknown type alias");
        acc.push({
          a: "alias",
          name,
          args: [this.typeOf(node.typeArguments[0])],
        });
        return;
      }
      if (!this.typeParams.has(name))
        this.fail(node, "unknown type parameter");
      acc.push({ a: "param", name });
      return;
    }

    if (ts.isLiteralTypeNode(node)) {
      // `literal` is declared as a bare Node, so it too is read by predicate.
      const lit = node.literal;
      if (lit.kind === ts.SyntaxKind.NullKeyword) {
        acc.push({ a: "null" });
        return;
      }
      if (ts.isStringLiteral(lit)) {
        acc.push({ a: "stringlit", v: lit.text });
        return;
      }
      if (ts.isNumericLiteral(lit)) {
        if (!DECIMAL.test(lit.text))
          this.fail(lit, "non-decimal numeric literal type");
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
      this.fail(lit, "literal type outside the fragment");
    }

    switch (node.kind) {
      // Keyword types carry nothing to read: the kind is the whole node.
      case ts.SyntaxKind.NeverKeyword:
        // The empty union: no atoms. Nothing inhabits it, so it contributes
        // nothing to the alternatives a value of this type may take.
        return;

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
      // A `void` result: no usable guarantee about the value.
      case ts.SyntaxKind.VoidKeyword:
        acc.push({ a: "void" });
        return;
      case ts.SyntaxKind.UnknownKeyword:
        this.top = true;
        return;

      default:
        this.fail(
          node,
          `type outside the fragment (${ts.SyntaxKind[node.kind]})`,
        );
    }
  }

  /** Whether the type being read mentioned `unknown`, which absorbs the
   * rest of its union: semantic top. */
  private top = false;

  typeOf(node: TypeNode | undefined): ClaimType {
    if (!node) this.fail(null, "missing type annotation");
    const atoms: Atom[] = [];
    this.top = false;
    this.atomsOf(node, atoms);
    const top = this.top;
    this.top = false;
    return top ? { top: true, atoms: [] } : { top: false, atoms };
  }

  /* ------------------------------------------------------- expressions -- */

  expr(node: Expression): Expr {
    // As in `atomsOf`: Expression is one base interface, so each form of
    // expression is recognized by its own predicate.
    if (ts.isParenthesizedExpression(node))
      // Parentheses carry no meaning of their own, but the producer records
      // the type of a parenthesized expression at the span of the outermost
      // parenthesis. Unwrap, and widen the span to match, so the two agree
      // on the key. Nested parentheses widen again at each level.
      return { ...this.expr(node.expression), pos: this.span(node) };

    if (ts.isConditionalExpression(node))
      return {
        k: "conditional",
        pos: this.span(node),
        cond: this.expr(node.condition),
        then: this.expr(node.whenTrue),
        else_: this.expr(node.whenFalse),
      };

    if (ts.isIdentifier(node)) {
      if (node.text === "undefined")
        return { k: "lit", pos: this.span(node), lit: { a: "undefined" } };
      return { k: "id", pos: this.span(node), name: node.text };
    }

    if (node.kind === ts.SyntaxKind.NullKeyword)
      return { k: "lit", pos: this.span(node), lit: { a: "null" } };
    if (node.kind === ts.SyntaxKind.TrueKeyword)
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "booleanlit", v: "true" },
      };
    if (node.kind === ts.SyntaxKind.FalseKeyword)
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "booleanlit", v: "false" },
      };

    if (ts.isStringLiteral(node))
      // `text` is the DECODED value, which is what a literal type denotes.
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "stringlit", v: node.text },
      };

    if (ts.isNumericLiteral(node)) {
      if (!DECIMAL.test(node.text))
        this.fail(node, "non-decimal numeric literal");
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: node.text },
      };
    }

    if (ts.isArrowFunction(node)) return this.lambda(node);

    if (ts.isObjectLiteralExpression(node)) {
      if (!node.properties.length)
        this.fail(node, "a record with no field has no location");
      const seen = new Set<string>();
      const fields = node.properties.map((f) => {
        if (!ts.isPropertyAssignment(f) || !ts.isIdentifier(f.name))
          this.fail(
            f,
            "expected a plain property; no accessors, methods or spreads",
          );
        const name =
          ts.isPropertyAssignment(f) && ts.isIdentifier(f.name)
            ? f.name.text
            : this.fail(f, "expected a plain property");
        if (seen.has(name)) this.fail(f, "duplicate field name in a record");
        if (name === "__proto__")
          this.fail(f, "prototype initializers are outside the fragment");
        seen.add(name);
        return {
          name,
          e: this.expr(
            ts.isPropertyAssignment(f)
              ? f.initializer
              : this.fail(f, "expected a plain property"),
          ),
        };
      });
      return { k: "alloc", pos: this.span(node), fields };
    }

    if (ts.isPropertyAccessExpression(node)) {
      if (node.questionDotToken)
        this.fail(node, "optional property access is outside the fragment");
      return {
        k: "read",
        pos: this.span(node),
        field: node.name.text,
        e: this.expr(node.expression),
      };
    }

    if (ts.isElementAccessExpression(node)) {
      if (node.questionDotToken)
        this.fail(node, "optional element access is outside the fragment");
      return {
        k: "index",
        pos: this.span(node),
        e: this.expr(node.expression),
        key: this.expr(node.argumentExpression),
      };
    }

    if (ts.isTypeOfExpression(node))
      return {
        k: "typeof",
        pos: this.span(node),
        e: this.expr(node.expression),
      };

    // A type assertion is the operand's value; the runtime never sees it.
    // What it asserts is an obligation on the operand, never a fact.
    if (ts.isAsExpression(node) || ts.isSatisfiesExpression(node))
      return {
        k: "cast",
        pos: this.span(node),
        cast: ts.isAsExpression(node) ? "as" : "satisfies",
        annot: this.typeOf(node.type),
        e: this.expr(node.expression),
      };
    if (ts.isNonNullExpression(node))
      return {
        k: "cast",
        pos: this.span(node),
        cast: "nonNull",
        annot: null,
        e: this.expr(node.expression),
      };

    if (ts.isPostfixUnaryExpression(node))
      return this.update(node, node.operand, node.operator, null, true);
    if (
      ts.isPrefixUnaryExpression(node) &&
      (node.operator === ts.SyntaxKind.PlusPlusToken ||
        node.operator === ts.SyntaxKind.MinusMinusToken)
    )
      return this.update(node, node.operand, node.operator, null, false);

    if (ts.isPrefixUnaryExpression(node)) {
      if (node.operator !== ts.SyntaxKind.ExclamationToken)
        this.fail(node, "unary operator outside the fragment");
      return { k: "not", pos: this.span(node), e: this.expr(node.operand) };
    }

    if (ts.isBinaryExpression(node)) return this.binary(node);

    if (ts.isCallExpression(node)) {
      if (ts.isPropertyAccessExpression(node.expression) &&
          ts.isIdentifier(node.expression.expression) && node.expression.expression.text === "Object" &&
          node.expression.name.text === "assign") {
        if (node.questionDotToken || node.expression.questionDotToken ||
            node.typeArguments?.length !== 2 || node.arguments.length !== 2 ||
            !ts.isArrowFunction(node.arguments[0]) || !ts.isObjectLiteralExpression(node.arguments[1]))
          this.fail(node, "Object.assign requires a fresh arrow, an object literal and two explicit type arguments");
        // The fragment cannot assign to Object.assign or pass Object as a value.
        // Reject any local declaration that could shadow the standard builtin.
        const checkBinding = (n: Node): void => {
          if ((ts.isParameterDeclaration(n) || ts.isVariableDeclaration(n) || ts.isFunctionDeclaration(n)) &&
              n.name && ts.isIdentifier(n.name) && n.name.text === "Object")
            this.fail(n, "shadowing Object is outside intrinsic callable initialization");
          n.forEachChild(checkBinding);
        };
        checkBinding(this.file);
        // These names either replace an intrinsic used by the lowering or
        // encounter special/non-writable properties on JavaScript functions.
        for (const property of node.arguments[1].properties) {
          if (ts.isPropertyAssignment(property) && ts.isIdentifier(property.name) &&
              ["call", "bind", "name", "length", "caller", "arguments", "__proto__"].includes(property.name.text))
            this.fail(property, "special function properties are outside callable initialization");
        }
        return {k: "withValue", pos: this.span(node), fn: this.expr(node.arguments[0]),
          initial: this.expr(node.arguments[1]), functionType: this.typeOf(node.typeArguments[0]),
          bagType: this.typeOf(node.typeArguments[1])};
      }
      if (ts.isPropertyAccessExpression(node.expression) && ["call", "bind"].includes(node.expression.name.text)) {
        if (node.questionDotToken || node.expression.questionDotToken || node.typeArguments?.length ||
            node.arguments.length === 0 || node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
            !this.localArrow(node.expression.expression))
          this.fail(node, `.${node.expression.name.text} requires a known local arrow, an explicit receiver and ordinary arguments`);
        return {k: node.expression.name.text === "bind" ? "bindWithReceiver" : "callWithReceiver", pos: this.span(node), callee: this.expr(node.expression.expression),
          receiver: this.expr(node.arguments[0]), args: node.arguments.slice(1).map((arg) => this.expr(arg))};
      }
      if (
        node.questionDotToken ||
        node.typeArguments?.length ||
        node.arguments.some((arg) => ts.isSpreadElement(arg))
      )
        this.fail(node, "expected ordinary call arguments without spread or type arguments");
      return {
        k: "apply",
        pos: this.span(node),
        callee: this.expr(node.expression),
        args: node.arguments.map((arg) => this.expr(arg)),
      };
    }

    this.fail(
      node,
      `expression outside the fragment (${ts.SyntaxKind[node.kind]})`,
    );
  }

  // A call signature alone does not establish the inherited .call intrinsic.
  // Follow immutable lexical aliases to source-created arrows. Parameters and
  // arbitrary call results may carry their own .call property, so are refused.
  private localArrow(node: Expression, seen = new Set<number>()): boolean {
    if (ts.isParenthesizedExpression(node)) return this.localArrow(node.expression, seen);
    if (ts.isArrowFunction(node)) return true;
    if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
        ts.isIdentifier(node.expression.expression) && node.expression.expression.text === "Object" &&
        node.expression.name.text === "assign")
      // Its initializer is separately parsed through the full Object.assign
      // gate. Do not parse it again here: its body may refer back to this name.
      return node.arguments.length === 2 && ts.isArrowFunction(node.arguments[0]) &&
        ts.isObjectLiteralExpression(node.arguments[1]);
    if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
        node.expression.name.text === "bind")
      return this.localArrow(node.expression.expression, seen);
    if (!ts.isIdentifier(node)) return false;
    // Held as a string: a narrowing of `node` does not reach into a closure.
    const name = node.text;
    for (let scope = node.parent; scope; scope = scope.parent) {
      if (ts.isBlock(scope)) {
        for (const statement of scope.statements) {
          if (!ts.isVariableStatement(statement)) continue;
          for (const decl of statement.declarationList.declarations) {
            if (!ts.isIdentifier(decl.name) || decl.name.text !== name) continue;
            if (!(statement.declarationList.flags & ts.NodeFlags.Const) || !decl.initializer || seen.has(decl.getStart(this.file))) return false;
            seen.add(decl.getStart(this.file));
            return this.localArrow(decl.initializer, seen);
          }
        }
      }
      if (ts.isFunctionLikeDeclaration(scope) && scope.parameters?.some((p) =>
          ts.isIdentifier(p.name) && p.name.text === name)) return false;
    }
    return false;
  }

  /** A compound assignment or an increment: the target's parts are evaluated
   * once, so the verifier is handed one form rather than a rewrite that would
   * evaluate an effectful key twice. */
  private update(
    node: Expression,
    target: Expression,
    token: ts.SyntaxKind,
    rhs: Expression | null,
    post: boolean,
  ): Expr {
    const ops: Record<number, ArithOp> = {
      [ts.SyntaxKind.PlusEqualsToken]: "add",
      [ts.SyntaxKind.MinusEqualsToken]: "sub",
      [ts.SyntaxKind.AsteriskEqualsToken]: "mul",
      [ts.SyntaxKind.SlashEqualsToken]: "div",
      [ts.SyntaxKind.PlusPlusToken]: "add",
      [ts.SyntaxKind.MinusMinusToken]: "sub",
    };
    const op = ops[token];
    if (!op) this.fail(node, `binary operator outside the fragment (${ts.tokenToString(token)})`);
    const lhs = this.expr(target);
    if (lhs.k !== "id" && lhs.k !== "read" && lhs.k !== "index")
      this.fail(target, "only field and local assignments are supported");
    return {
      k: "update",
      pos: this.span(node),
      op,
      target: lhs,
      rhs: rhs ? this.expr(rhs) : null,
      post,
    };
  }

  private binary(node: BinaryExpression): Expr {
    switch (node.operatorToken.kind) {
      case ts.SyntaxKind.PlusEqualsToken:
      case ts.SyntaxKind.MinusEqualsToken:
      case ts.SyntaxKind.AsteriskEqualsToken:
      case ts.SyntaxKind.SlashEqualsToken:
        return this.update(node, node.left, node.operatorToken.kind, node.right, false);
    }
    const arithmetic: Record<number, ArithOp> = {
      [ts.SyntaxKind.PlusToken]: "add",
      [ts.SyntaxKind.MinusToken]: "sub",
      [ts.SyntaxKind.AsteriskToken]: "mul",
      [ts.SyntaxKind.SlashToken]: "div",
    };
    const arith = arithmetic[node.operatorToken.kind];
    if (arith)
      return { k: "arith", pos: this.span(node), op: arith, l: this.expr(node.left), r: this.expr(node.right) };
    const logical: Record<number, "nullish" | "or" | "and"> = {
      [ts.SyntaxKind.QuestionQuestionEqualsToken]: "nullish",
      [ts.SyntaxKind.BarBarEqualsToken]: "or",
      [ts.SyntaxKind.AmpersandAmpersandEqualsToken]: "and",
    };
    const logicalOp = logical[node.operatorToken.kind];
    if (logicalOp && (logicalOp !== "nullish" || !ts.isIdentifier(node.left))) {
      const target = this.expr(node.left);
      if (target.k !== "id" && target.k !== "read" && target.k !== "index")
        this.fail(node.left, "only field and local assignments are supported");
      if (target.k === "id" && target.name === "undefined")
        this.fail(node.left, "shadowing undefined is outside the fragment");
      return { k: "logicalAssign", pos: this.span(node), op: logicalOp, target, rhs: this.expr(node.right) };
    }
    if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionEqualsToken) {
      if (!ts.isIdentifier(node.left) || node.left.text === "undefined")
        this.fail(node.left, "nullish assignment requires a local identifier");
      return {
        k: "nullishAssign",
        pos: this.span(node),
        name: node.left.text,
        namePos: this.span(node.left),
        rhs: this.expr(node.right),
      };
    }
    if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken)
      return {
        k: "coalesce",
        pos: this.span(node),
        left: this.expr(node.left),
        right: this.expr(node.right),
      };
    if (node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      // Assigning a name is assigning a mutable local. Whether one was
      // declared is the adapter's to check: it builds the scope, and a name
      // that is not a mutable local there has no slot to write.
      if (ts.isIdentifier(node.left)) {
        if (node.left.text === "undefined")
          this.fail(node.left, "shadowing undefined is outside the fragment");
        return {
          k: "assign",
          pos: this.span(node),
          name: node.left.text,
          namePos: this.span(node.left),
          rhs: this.expr(node.right),
        };
      }
      if (ts.isElementAccessExpression(node.left) && !node.left.questionDotToken)
        return {
          k: "indexWrite",
          pos: this.span(node),
          receiver: this.expr(node.left.expression),
          key: this.expr(node.left.argumentExpression),
          rhs: this.expr(node.right),
        };
      if (
        !ts.isPropertyAccessExpression(node.left) ||
        node.left.questionDotToken
      )
        this.fail(node.left, "only field and local assignments are supported");
      return {
        k: "write",
        pos: this.span(node),
        field: ts.isPropertyAccessExpression(node.left)
          ? node.left.name.text
          : this.fail(node.left, "only field and local assignments are supported"),
        receiver: this.expr(
          ts.isPropertyAccessExpression(node.left)
            ? node.left.expression
            : this.fail(node.left, "only field and local assignments are supported"),
        ),
        rhs: this.expr(node.right),
      };
    }
    const ops: Record<number, string> = {
      [ts.SyntaxKind.EqualsEqualsEqualsToken]: "===",
      [ts.SyntaxKind.ExclamationEqualsEqualsToken]: "!==",
      [ts.SyntaxKind.AmpersandAmpersandToken]: "&&",
      [ts.SyntaxKind.BarBarToken]: "||",
    };
    const op = ops[node.operatorToken.kind];
    if (!op)
      this.fail(
        node,
        `binary operator outside the fragment (${this.text(node.operatorToken)})`,
      );
    if (op === "===" || op === "!==") {
      const unwrap = (e: Expression): Expression => ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e;
      const left = unwrap(node.left), right = unwrap(node.right);
      const pair = ts.isTypeOfExpression(left) && ts.isStringLiteral(right) && right.text === "function"
        ? left : ts.isTypeOfExpression(right) && ts.isStringLiteral(left) && left.text === "function"
          ? right : null;
      if (pair)
        return {k: "functionTest", pos: this.span(node), equal: op === "===", e: this.expr(pair.expression)};
    }
    return {
      k: "bin",
      pos: this.span(node),
      op,
      l: this.expr(node.left),
      r: this.expr(node.right),
    };
  }

  /* ----------------------------------------------------------- closures -- */
  // A closure body is an expression in the calculus. A block-bodied one is
  // lowered here, once, so the verifier never has to guess how statements
  // inside a closure become one: the parser owns that translation because it
  // owns what the source means.

  private lambda(node: ArrowFunction): Expr {
    if (node.modifiers?.length || node.typeParameters?.length)
      this.fail(node, "expected a non-generic synchronous closure");
    // Each name is taken where its parameter has just been checked: a
    // narrowing does not survive into the second pass over the same list.
    const names = node.parameters.map((p) => {
      if (
        !ts.isIdentifier(p.name) ||
        p.name.text === "this" ||
        p.questionToken ||
        p.dotDotDotToken ||
        p.initializer
      )
        this.fail(p, "expected a required closure parameter");
      if (p.name.text === "undefined")
        this.fail(p, "shadowing undefined is outside the fragment");
      return p.name.text;
    });

    const result = () => this.typeOf(node.type);
    const body = ts.isBlock(node.body)
      ? this.closureBlock(
          node.body,
          node.body.statements.map((s) => this.stmt(s)),
          result,
        )
      : this.expr(node.body);
    return {
      k: "lambda",
      pos: this.span(node),
      params: node.parameters.map((p, i) => ({name: names[i], type: this.typeOf(p.type)})),
      result: this.typeOf(node.type),
      body,
    };
  }

  private closureBlock(
    at: Node,
    statements: Stmt[],
    result: () => ClaimType,
  ): Expr {
    const hasReturn = (xs: Stmt[]): boolean =>
      xs.some(
        (st) =>
          st.k === "return" ||
          (st.k === "if" && (hasReturn(st.then) || hasReturn(st.else_ ?? []))),
      );
    const returns = (xs: Stmt[]): boolean => {
      const last = xs.at(-1);
      return (
        last?.k === "return" ||
        (last?.k === "if" && returns(last.then) && returns(last.else_ ?? []))
      );
    };

    const prefix = (stmts: Stmt[], tail: Expr, allowReturn = false): Expr => {
      for (let i = stmts.length - 1; i >= 0; --i) {
        const st = stmts[i];
        if (st.k === "while" || st.k === "break" || st.k === "continue")
          this.fail(
            at,
            "loops inside closures require a graph-backed call/body interface",
          );
        if (st.k === "if") {
          const yes = st.then,
            no = st.else_ ?? [];
          const arm = (xs: Stmt[]) =>
            prefix(xs, { k: "doneBody", pos: st.pos });
          if (!hasReturn(yes) && !hasReturn(no)) {
            const init: Expr = {
              k: "ifBody",
              pos: st.pos,
              result: NULL_TYPE,
              cond: st.cond,
              then: arm(yes),
              else_: arm(no),
            };
            tail = { k: "seqBody", pos: st.pos, init, body: tail };
          } else if (
            allowReturn &&
            ((returns(yes) && !hasReturn(no)) ||
              (returns(no) && !hasReturn(yes)))
          ) {
            // Finish the falling arm in its own scope before the continuation.
            const resume = (xs: Stmt[]): Expr =>
              xs.length === 0
                ? tail
                : { k: "seqBody", pos: st.pos, init: arm(xs), body: tail };
            tail = {
              k: "ifBody",
              pos: st.pos,
              result: result(),
              cond: st.cond,
              then: returns(yes) ? block(yes) : resume(yes),
              else_: returns(no) ? block(no) : resume(no),
            };
          } else
            this.fail(
              at,
              "closure branch needs one returning arm and one return-free arm",
            );
        } else if (st.k === "pattern") {
          this.fail(at, "a pattern in a closure body is outside the fragment");
        } else if (st.k === "const" || st.k === "effect") {
          // A lowered binding is an entry of its own, and a producer states
          // one entry per statement: a list of declarators has no entry for
          // its later bindings inside a closure body.
          if (st.k === "const" && st.bindings.length !== 1)
            this.fail(at, "one binding per `const` in a closure body");
          const bound = st.k === "const" ? st.bindings[0] : null;
          tail = {
            k: "letBody",
            pos: st.pos,
            name: bound ? bound.name : "",
            annot: bound ? bound.annot : null,
            init: st.k === "const" ? st.bindings[0].init : st.e,
            body: tail,
          };
        } else
          this.fail(
            at,
            "statements after an unconditional return are outside the fragment",
          );
      }
      return tail;
    };

    const block = (stmts: Stmt[]): Expr => {
      const last = stmts.at(-1);
      let tail: Expr;
      if (last?.k === "return")
        tail = { k: "returnBody", pos: last.pos, e: last.e };
      else if (last?.k === "if" && last.else_ !== null)
        tail = {
          k: "ifBody",
          pos: last.pos,
          result: result(),
          cond: last.cond,
          then: block(last.then),
          else_: block(last.else_),
        };
      else this.fail(at, "closure block must return on both terminal arms");
      return prefix(stmts.slice(0, -1), tail, true);
    };

    return block(statements);
  }

  /* -------------------------------------------------------- statements -- */

  /* `const { field: name = default, … } = init;`. One declarator, identifier
     keys and names, no rest, no nesting: what the lowering states. */
  private patternStmt(node: VariableStatement, mutable: boolean): Stmt {
    const list = node.declarationList;
    if (mutable) this.fail(node, "a `let` pattern is outside the fragment");
    if (list.declarations.length !== 1)
      this.fail(node, "a pattern declares alone in the fragment");
    const d = list.declarations[0];
    const pattern = d.name;
    if (!ts.isObjectBindingPattern(pattern))
      this.fail(d, "destructuring is outside the fragment");
    if (d.type) this.fail(d, "an annotated pattern is outside the fragment");
    if (!d.initializer) this.fail(d, "a `const` needs an initializer");
    if (pattern.elements.length === 0)
      this.fail(pattern, "an empty pattern binds nothing");
    const names = new Set<string>();
    const props: PatternPropAst[] = pattern.elements.map((el) => {
      if (el.dotDotDotToken)
        this.fail(el, "rest elements are outside the fragment");
      if (!el.name || !ts.isIdentifier(el.name))
        this.fail(el, "nested patterns are outside the fragment");
      const key = el.propertyName ?? el.name;
      if (!ts.isIdentifier(key))
        this.fail(el, "computed or string pattern keys are outside the fragment");
      if (el.name.text === "undefined")
        this.fail(el, "shadowing undefined is outside the fragment");
      if (names.has(el.name.text)) this.fail(el, "duplicate pattern binding");
      names.add(el.name.text);
      return {
        field: key.text,
        name: el.name.text,
        namePos: this.span(el.name),
        default_: el.initializer ? this.expr(el.initializer) : null,
      };
    });
    return {
      k: "pattern",
      pos: this.span(node),
      props,
      init: this.expr(d.initializer),
    };
  }

  /* A branch or loop body. TypeScript allows a single statement where a block
     could be written, and the two mean the same thing here: a lexical
     declaration cannot be an unbraced body, so no binding's scope depends on
     the braces. */
  block(node: Statement): Stmt[] {
    if (!ts.isBlock(node)) {
      if (ts.isVariableStatement(node))
        this.fail(node, "a declaration requires a block body");
      return [this.stmt(node)];
    }
    return node.statements.map((s) => this.stmt(s));
  }

  stmt(node: Statement): Stmt {
    if (ts.isExpressionStatement(node))
      return {
        k: "effect",
        pos: this.span(node),
        e: this.expr(node.expression),
      };

    if (ts.isReturnStatement(node)) {
      if (!node.expression)
        this.fail(node, "a bare `return` is outside the fragment");
      return {
        k: "return",
        pos: this.span(node),
        e: this.expr(node.expression),
      };
    }

    if (ts.isVariableStatement(node)) {
      const list = node.declarationList;
      const mutable = !(list.flags & ts.NodeFlags.Const);
      // `var` is function-scoped and hoisted, so it is not this binding form.
      if (mutable && !(list.flags & ts.NodeFlags.Let))
        this.fail(node, "`var` is outside the fragment");
      const kindWord = mutable ? "let" : "const";
      if (list.declarations.some((d) => ts.isObjectBindingPattern(d.name)))
        return this.patternStmt(node, mutable);
      // A declaration list binds its declarators left to right, each
      // initializer seeing the earlier bindings, under the statement's one
      // entry. Each declarator is gated on its own terms.
      const bindings: BindingAst[] = list.declarations.map((d) => {
        if (d.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(d, "destructuring is outside the fragment");
        if (d.name.text === "undefined")
          this.fail(d, "shadowing undefined is outside the fragment");
        if (!d.initializer)
          this.fail(d, `a \`${kindWord}\` needs an initializer`);
        // For `let`, the storage contract is what every later assignment is
        // checked against. Written, it is the annotation; unwritten, the
        // producer states one for the binding and the adapter checks that,
        // rather than this taking the initializer's type for the contract.
        return {
          name: d.name.text,
          namePos: this.span(d.name),
          annot: d.type ? this.typeOf(d.type) : null,
          init: this.expr(d.initializer),
        };
      });
      if (mutable) return { k: "let", pos: this.span(node), bindings };
      return { k: "const", pos: this.span(node), bindings };
    }

    if (ts.isBreakStatement(node) || ts.isContinueStatement(node)) {
      if (node.label)
        this.fail(node, "only unlabeled loop transfers are supported");
      // The nearest enclosing loop, not crossing into another function.
      let parent = node.parent;
      while (
        parent &&
        !ts.isFunctionLikeDeclaration(parent) &&
        !ts.isWhileStatement(parent)
      )
        parent = parent.parent;
      if (!parent || !ts.isWhileStatement(parent))
        this.fail(node, "break or continue outside a supported loop");
      return {
        k: ts.isBreakStatement(node) ? "break" : "continue",
        pos: this.span(node),
      };
    }

    if (ts.isWhileStatement(node))
      return {
        k: "while",
        pos: this.span(node),
        cond: this.expr(node.expression),
        body: this.block(node.statement),
      };

    if (ts.isIfStatement(node)) {
      if (
        node.elseStatement &&
        node.elseStatement.kind !== ts.SyntaxKind.Block
      )
        this.fail(
          node.elseStatement,
          "`else if` and non-block branches are outside the fragment",
        );
      return {
        k: "if",
        pos: this.span(node),
        cond: this.expr(node.expression),
        then: this.block(node.thenStatement),
        else_: node.elseStatement ? this.block(node.elseStatement) : null,
      };
    }

    this.fail(
      node,
      `statement outside the fragment (${ts.SyntaxKind[node.kind]})`,
    );
  }

  /* ---------------------------------------------------------- aliases -- */

  aliasDecl(node: TypeAliasDeclaration): TypeAliasAst {
    if (!node.name) this.fail(node, "anonymous type alias");
    if (node.name.text === "undefined")
      this.fail(node, "shadowing undefined is outside the fragment");
    if (node.modifiers?.length)
      this.fail(node, "modifiers (export/declare) are outside the fragment");
    if (!node.typeParameters || node.typeParameters.length !== 1)
      this.fail(node, "only one type parameter is in the fragment");
    const tp = node.typeParameters[0];
    if (tp.constraint || tp.defaultType)
      this.fail(
        tp,
        "type parameter bounds and defaults are outside the fragment",
      );
    if (tp.name.kind !== ts.SyntaxKind.Identifier)
      this.fail(tp, "expected a type-parameter name");
    const param = tp.name.text;
    this.typeParams.add(param);
    this.aliasApps = false;
    try {
      return {
        name: node.name.text,
        typeParams: [{ name: param, bound: null }],
        body: this.typeOf(node.type),
      };
    } finally {
      this.typeParams.clear();
    }
  }

  /* --------------------------------------------------------- functions -- */

  functionDecl(node: FunctionDeclaration): FunctionAst {
    if (!node.name) this.fail(node, "anonymous function");
    if (node.name.text === "undefined")
      this.fail(node, "shadowing undefined is outside the fragment");
    if (node.modifiers?.length)
      this.fail(
        node,
        "modifiers (export/async/declare) are outside the fragment",
      );
    if (!node.body) this.fail(node, "a function must have a body");
    const typeParams: TypeParamAst[] = [];
    if (node.typeParameters?.length) {
      for (const tp of node.typeParameters) {
        if (tp.defaultType)
          this.fail(tp, "type parameter defaults are outside the fragment");
        if (tp.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(tp, "expected a type-parameter name");
        if (this.typeParams.has(tp.name.text))
          this.fail(tp, "duplicate type parameter");
        let bound: ClaimType | null = null;
        if (tp.constraint) {
          const earlier = ts.isTypeReferenceNode(tp.constraint) &&
            tp.constraint.typeName.kind === ts.SyntaxKind.Identifier &&
            !tp.constraint.typeArguments?.length &&
            this.typeParams.has(tp.constraint.typeName.text);
          if (tp.constraint.kind !== ts.SyntaxKind.BooleanKeyword && !earlier)
            this.fail(tp.constraint,
              "only `extends boolean` or an earlier type parameter is in the fragment");
          bound = this.typeOf(tp.constraint);
        }
        typeParams.push({ name: tp.name.text, bound });
        this.typeParams.add(tp.name.text);
      }
    }
    try {
    const params = node.parameters.map((p) => {
      if (p.name.kind !== ts.SyntaxKind.Identifier)
        this.fail(p, "destructuring parameter");
      if (p.name.text === "undefined")
        this.fail(p, "shadowing undefined is outside the fragment");
      if (p.questionToken)
        this.fail(p, "optional parameters are outside the fragment");
      if (p.dotDotDotToken)
        this.fail(p, "rest parameters are outside the fragment");
      if (p.initializer)
        this.fail(p, "default parameters are outside the fragment");
      return {
        name: p.name.text,
        pos: this.span(p.name),
        type: this.typeOf(p.type),
      };
    });
    return {
      name: node.name.text,
      namePos: this.span(node.name),
      typeParams,
      params,
      retType: this.typeOf(node.type),
      body: this.block(node.body),
    };
    } finally {
      this.typeParams.clear();
    }
  }
}

/* ------------------------------------------------------------- parsing -- */

/**
 * The whole file, or a gate rejection. A rejection is an Error whose message
 * begins "gate: ", which is what the command writes to stderr, so a caller and
 * the command report one wording.
 *
 * `carriesContext` is for a caller that assembled the file itself and put
 * declarations beside the function it is asking about — the census does, so
 * that a function is typed with the names its own file declares rather than
 * failing for what extracting it left behind. Those declarations are then not
 * the subject: they are skipped rather than rejected, and nothing about them
 * is verified. A type they introduce still has to be sayable in a claim, so a
 * function that depends on one fails on that claim, in its own words.
 */
export function parseFile(file: string, carriesContext = false): Ast {
  const absolute = resolve(file);
  const text = readFileSync(absolute, "utf8");
  const source = openFile(absolute, text);
  const gate = new Gate(source);
  const aliasNodes: TypeAliasDeclaration[] = [];
  const fnNodes: FunctionDeclaration[] = [];
  for (const s of source.statements) {
    if (ts.isTypeAliasDeclaration(s)) aliasNodes.push(s);
    else if (ts.isFunctionDeclaration(s)) fnNodes.push(s);
    else if (carriesContext) continue;
    else
      gate.fail(
        s,
        `top-level statement outside the fragment (${ts.SyntaxKind[s.kind]})`,
      );
  }
  // Carried context holds aliases this fragment cannot state — more than one
  // parameter, a bound, none at all. They are skipped rather than rejected,
  // on the same terms as the other declarations: unregistered, so a function
  // that names one fails on that name instead of on its neighbour's shape.
  const statable = (n: TypeAliasDeclaration): boolean => {
    const tp = n.typeParameters;
    return (
      !n.modifiers?.length &&
      tp?.length === 1 &&
      !tp[0].constraint &&
      !tp[0].defaultType
    );
  };
  const stated = carriesContext ? aliasNodes.filter(statable) : aliasNodes;
  for (const node of stated) {
    if (!node.name) gate.fail(node, "anonymous type alias");
    gate.registerAlias(node.name.text, node);
  }
  const aliases = stated.map((s) => gate.aliasDecl(s));
  gate.enableAliasApps();
  // A function without a body is a declaration, not an example of one.
  const declared = carriesContext ? fnNodes.filter((s) => s.body) : fnNodes;
  const functions = declared.map((s) => gate.functionDecl(s));
  if (functions.length === 0) gate.fail(null, "no functions in file");
  return {
    file,
    sourceSha256: createHash("sha256").update(text).digest("hex"),
    aliases,
    functions,
  };
}

/**
 * The functions a file defines, named and with a body, whether or not the
 * fragment admits them. A report has to be able to name what it did not
 * cover, and that is exactly the case a gate rejection would otherwise hide,
 * so this reads the compiler's tree directly and applies no gate.
 */
export function definedFunctions(
  file: string,
): { name: string; namePos: Span }[] {
  const absolute = resolve(file);
  const source = projectFor(absolute).program.getSourceFile(absolute);
  if (!source) throw new Error(`the compiler produced no tree for ${file}`);
  const out: { name: string; namePos: Span }[] = [];
  for (const statement of source.statements)
    if (ts.isFunctionDeclaration(statement) && statement.name && statement.body)
      out.push({
        name: statement.name.text,
        namePos: [statement.name.getStart(source), statement.name.end],
      });
  return out;
}

/**
 * The fragment's reading of one type annotation, for a trusted tool that has a
 * node and needs the type the gate would give it. The annotation's own file is
 * the place a rejection names, which is why the node carries it.
 */
export function typeOf(node: TypeNode): ClaimType {
  return new Gate(node.getSourceFile()).typeOf(node);
}

/* ---------------------------------------------------------------- main -- */

// Run as a command, or lend the type translation to another trusted tool. The
// annotation encoding must have exactly one implementation: a second one would
// be a second opinion about what a source type means.
if (process.argv[1] && import.meta.filename === resolve(process.argv[1])) {
  const file = process.argv[2];
  if (!file) {
    process.stderr.write("usage: fragment-parse.ts <file.ts>\n");
    process.exit(2);
  }
  try {
    process.stdout.write(JSON.stringify(parseFile(file), null, 1));
    close();
  } catch (error) {
    process.stderr.write(messageOf(error) + "\n");
    process.exit(1);
  }
}
