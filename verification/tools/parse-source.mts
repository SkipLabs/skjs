#!/usr/bin/env node
/*
 * Trusted front end for the verification experiment (see verification/DESIGN.md).
 *
 * Reads a .ts file and emits its abstract syntax tree as JSON, with every node
 * carrying its [start, end) offsets in UTF-16 code units. This program is the
 * SYNTACTIC GATE: a construct outside the fragment is an error, so a program it
 * rejects can never be certified. Anything it accepts, it describes exactly.
 *
 * This program is TRUSTED. It defines what the source text means; the verifier
 * never sees the producer's own parse. The fragment it accepts is stated in
 * ../AGENTS.md and, as a grammar, in the pull request description.
 */
import { API } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";

/* ------------------------------------------------------------ the tree -- */
// What the verifier decodes (SourceInput.decodeAst). The shapes are structural
// on purpose: this is a wire format, and its field names are the contract.

/** A half-open span of the source, in UTF-16 code units. */
export type Span = [start: number, end: number];

/** A type as the claim format writes it: a union of atoms, or everything. */
export interface WireType {
  top: boolean;
  atoms: Atom[];
}

export type Atom =
  | { a: "null" | "undefined" | "boolean" | "string" | "number" }
  | { a: "stringlit" | "numberlit" | "booleanlit"; v: string }
  | {
      a: "record";
      fields: {
        name: string;
        optional: boolean;
        read: WireType;
        write: WireType;
      }[];
      indexes: { string: string; number: string; symbol: string };
      call: string;
      construct: string;
      array: string;
      and?: Atom[];
    }
  | {
      a: "function";
      params: WireType[];
      result: WireType;
      construct: string;
      array: string;
      and?: Atom[];
    };

export type Expr =
  | { k: "id"; pos: Span; name: string }
  | { k: "lit"; pos: Span; lit: Atom }
  | { k: "not" | "alloc" | "read" | "typeof"; pos: Span; e: Expr }
  | { k: "bin"; pos: Span; op: string; l: Expr; r: Expr }
  | { k: "coalesce"; pos: Span; left: Expr; right: Expr }
  | { k: "write"; pos: Span; receiver: Expr; rhs: Expr }
  | { k: "apply"; pos: Span; callee: Expr; arg: Expr }
  | { k: "conditional"; pos: Span; cond: Expr; then: Expr; else_: Expr }
  | {
      k: "lambda";
      pos: Span;
      name: string;
      arg: WireType;
      result: WireType;
      body: Expr;
    }
  /* A block-bodied closure, lowered to nested expressions: the calculus has no
     statements inside a closure, so the parser does the lowering the verifier
     would otherwise have to invent. */
  | { k: "doneBody"; pos: Span }
  | { k: "returnBody"; pos: Span; e: Expr }
  | { k: "seqBody"; pos: Span; init: Expr; body: Expr }
  | {
      k: "letBody";
      pos: Span;
      name: string;
      annot: WireType | null;
      init: Expr;
      body: Expr;
    }
  | {
      k: "ifBody";
      pos: Span;
      result: WireType;
      cond: Expr;
      then: Expr;
      else_: Expr;
    };

export type Stmt =
  | { k: "effect"; pos: Span; e: Expr }
  | { k: "return"; pos: Span; e: Expr }
  | { k: "break" | "continue"; pos: Span }
  | { k: "while"; pos: Span; cond: Expr; body: Stmt[] }
  | { k: "if"; pos: Span; cond: Expr; then: Stmt[]; else_: Stmt[] | null }
  | {
      k: "const";
      pos: Span;
      name: string;
      namePos: Span;
      annot: WireType | null;
      init: Expr;
    };

export interface FunctionAst {
  name: string;
  namePos: Span;
  params: { name: string; pos: Span; type: WireType }[];
  retType: WireType;
  body: Stmt[];
}

export interface Ast {
  file: string;
  sourceSha256: string;
  functions: FunctionAst[];
}

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
    throw new Error(`gate: parse error: ${syntax[0]!.text}`);
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

/* ------------------------------------------------------- the predicates -- */
// The two the AST module does not carry, written against `kind` because that is
// all they ever were.

const FUNCTION_LIKE = new Set<number>([
  ts.SyntaxKind.FunctionDeclaration,
  ts.SyntaxKind.FunctionExpression,
  ts.SyntaxKind.ArrowFunction,
  ts.SyntaxKind.MethodDeclaration,
  ts.SyntaxKind.Constructor,
  ts.SyntaxKind.GetAccessor,
  ts.SyntaxKind.SetAccessor,
]);
const isFunctionLike = (n: Node) => FUNCTION_LIKE.has(n.kind);
const isPropertySignature = (n: Node) =>
  n.kind === ts.SyntaxKind.PropertySignature;

/* -------------------------------------------------------------- the gate -- */
// One parse owns one source file. `fail` and `span` are the only two things
// that need it, and they are the only two that should: a gate rejection names
// a place in the file it is reading.

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators, bigint) is outside it.
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

const NULL_TYPE: WireType = { top: false, atoms: [{ a: "null" }] };

class Gate {
  // Written out rather than a parameter property: node strips types, it does
  // not compile them, so the syntax has to be erasable.
  private readonly file: SourceFile;
  constructor(file: SourceFile) {
    this.file = file;
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

  atomsOf(node: any, acc: Atom[]): void {
    switch (node.kind) {
      case ts.SyntaxKind.ParenthesizedType:
        return this.atomsOf(node.type, acc);

      case ts.SyntaxKind.UnionType:
        for (const t of node.types) this.atomsOf(t, acc);
        return;

      case ts.SyntaxKind.FunctionType: {
        if (node.typeParameters?.length || node.parameters.length !== 1)
          this.fail(node, "expected a free unary function type");
        const p = node.parameters[0];
        if (
          !ts.isIdentifier(p.name) ||
          p.name.text === "this" ||
          p.questionToken ||
          p.dotDotDotToken ||
          p.initializer
        )
          this.fail(p, "expected a required ordinary parameter");
        acc.push({
          a: "function",
          params: [this.typeOf(p.type)],
          result: this.typeOf(node.type),
          construct: "unknown",
          array: "unknown",
        });
        return;
      }

      case ts.SyntaxKind.TypeLiteral: {
        if (node.members.length !== 1)
          this.fail(node, "expected a single cell field");
        const f = node.members[0];
        if (
          !isPropertySignature(f) ||
          !ts.isIdentifier(f.name) ||
          f.name.text !== "value" ||
          // A member's `?` (or `!`) is its postfix token; a parameter's is a
          // question token. Different nodes, different names.
          f.postfixToken ||
          f.modifiers?.length
        )
          this.fail(f, "expected required mutable value field");
        const t = this.typeOf(f.type);
        acc.push({
          a: "record",
          fields: [{ name: "value", optional: false, read: t, write: t }],
          indexes: { string: "absent", number: "absent", symbol: "absent" },
          call: "unknown",
          construct: "unknown",
          array: "unknown",
        });
        return;
      }

      case ts.SyntaxKind.IntersectionType: {
        // Union is the atom list; conjunction lives inside the atom kinds that
        // have one, mirroring the clause language, where only a location under
        // several contracts and a function with several signatures conjoin.
        // Nothing else does, so nothing else may be written here: a format
        // that could say `null & boolean` would say something no clause holds.
        // Conjunction is associative, so a parenthesized intersection inside
        // one contributes its operands to the same flat list.
        const operands: any[] = [];
        const flatten = (t: any) => {
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
          return one[0]!;
        });
        const head = parts[0]!;
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

      case ts.SyntaxKind.LiteralType: {
        const lit = node.literal;
        switch (lit.kind) {
          case ts.SyntaxKind.NullKeyword:
            acc.push({ a: "null" });
            return;
          case ts.SyntaxKind.StringLiteral:
            acc.push({ a: "stringlit", v: lit.text });
            return;
          case ts.SyntaxKind.NumericLiteral:
            if (!DECIMAL.test(lit.text))
              this.fail(lit, "non-decimal numeric literal type");
            acc.push({ a: "numberlit", v: lit.text });
            return;
          case ts.SyntaxKind.TrueKeyword:
            acc.push({ a: "booleanlit", v: "true" });
            return;
          case ts.SyntaxKind.FalseKeyword:
            acc.push({ a: "booleanlit", v: "false" });
            return;
          default:
            this.fail(lit, "literal type outside the fragment");
        }
      }

      default:
        this.fail(
          node,
          `type outside the fragment (${ts.SyntaxKind[node.kind]})`,
        );
    }
  }

  typeOf(node: any): WireType {
    if (!node) this.fail(null, "missing type annotation");
    const atoms: Atom[] = [];
    this.atomsOf(node, atoms);
    return { top: false, atoms };
  }

  /* ------------------------------------------------------- expressions -- */

  expr(node: any): Expr {
    switch (node.kind) {
      case ts.SyntaxKind.ParenthesizedExpression:
        // Parentheses carry no meaning of their own, but the producer records
        // the type of a parenthesized expression at the span of the outermost
        // parenthesis. Unwrap, and widen the span to match, so the two agree
        // on the key. Nested parentheses widen again at each level.
        return { ...this.expr(node.expression), pos: this.span(node) };

      case ts.SyntaxKind.ConditionalExpression:
        return {
          k: "conditional",
          pos: this.span(node),
          cond: this.expr(node.condition),
          then: this.expr(node.whenTrue),
          else_: this.expr(node.whenFalse),
        };

      case ts.SyntaxKind.Identifier:
        if (node.text === "undefined")
          return { k: "lit", pos: this.span(node), lit: { a: "undefined" } };
        return { k: "id", pos: this.span(node), name: node.text };

      case ts.SyntaxKind.NullKeyword:
        return { k: "lit", pos: this.span(node), lit: { a: "null" } };
      case ts.SyntaxKind.TrueKeyword:
        return {
          k: "lit",
          pos: this.span(node),
          lit: { a: "booleanlit", v: "true" },
        };
      case ts.SyntaxKind.FalseKeyword:
        return {
          k: "lit",
          pos: this.span(node),
          lit: { a: "booleanlit", v: "false" },
        };
      case ts.SyntaxKind.StringLiteral:
        // `text` is the DECODED value, which is what a literal type denotes.
        return {
          k: "lit",
          pos: this.span(node),
          lit: { a: "stringlit", v: node.text },
        };
      case ts.SyntaxKind.NumericLiteral:
        if (!DECIMAL.test(node.text))
          this.fail(node, "non-decimal numeric literal");
        return {
          k: "lit",
          pos: this.span(node),
          lit: { a: "numberlit", v: node.text },
        };

      case ts.SyntaxKind.ArrowFunction:
        return this.lambda(node);

      case ts.SyntaxKind.ObjectLiteralExpression: {
        if (node.properties.length !== 1)
          this.fail(node, "expected plain single-field allocation");
        const f = node.properties[0];
        if (
          !ts.isPropertyAssignment(f) ||
          !ts.isIdentifier(f.name) ||
          f.name.text !== "value"
        )
          this.fail(
            f,
            "expected plain value property; no accessors, methods or spreads",
          );
        return {
          k: "alloc",
          pos: this.span(node),
          e: this.expr(f.initializer),
        };
      }

      case ts.SyntaxKind.PropertyAccessExpression:
        if (node.questionDotToken || node.name.text !== "value")
          this.fail(node, "expected cell.value");
        return {
          k: "read",
          pos: this.span(node),
          e: this.expr(node.expression),
        };

      case ts.SyntaxKind.TypeOfExpression:
        return {
          k: "typeof",
          pos: this.span(node),
          e: this.expr(node.expression),
        };

      case ts.SyntaxKind.PrefixUnaryExpression:
        if (node.operator !== ts.SyntaxKind.ExclamationToken)
          this.fail(node, "unary operator outside the fragment");
        return { k: "not", pos: this.span(node), e: this.expr(node.operand) };

      case ts.SyntaxKind.BinaryExpression:
        return this.binary(node);

      case ts.SyntaxKind.CallExpression: {
        if (
          node.questionDotToken ||
          node.typeArguments?.length ||
          node.arguments.length !== 1 ||
          ts.isSpreadElement(node.arguments[0])
        )
          this.fail(node, "expected one ordinary call argument");
        return {
          k: "apply",
          pos: this.span(node),
          callee: this.expr(node.expression),
          arg: this.expr(node.arguments[0]),
        };
      }

      default:
        this.fail(
          node,
          `expression outside the fragment (${ts.SyntaxKind[node.kind]})`,
        );
    }
  }

  private binary(node: any): Expr {
    if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken)
      return {
        k: "coalesce",
        pos: this.span(node),
        left: this.expr(node.left),
        right: this.expr(node.right),
      };
    if (node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      if (
        !ts.isPropertyAccessExpression(node.left) ||
        node.left.questionDotToken ||
        node.left.name.text !== "value"
      )
        this.fail(node.left, "only cell.value assignments are supported");
      return {
        k: "write",
        pos: this.span(node),
        receiver: this.expr(node.left.expression),
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

  private lambda(node: any): Expr {
    if (
      node.modifiers?.length ||
      node.typeParameters?.length ||
      node.parameters.length !== 1
    )
      this.fail(node, "expected a unary closure");
    const p = node.parameters[0];
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

    const result = () => this.typeOf(node.type);
    const body = ts.isBlock(node.body)
      ? this.closureBlock(
          node.body,
          node.body.statements.map((s: any) => this.stmt(s)),
          result,
        )
      : this.expr(node.body);
    return {
      k: "lambda",
      pos: this.span(node),
      name: p.name.text,
      arg: this.typeOf(p.type),
      result: this.typeOf(node.type),
      body,
    };
  }

  private closureBlock(
    at: Node,
    statements: Stmt[],
    result: () => WireType,
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
        const st = stmts[i]!;
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
        } else if (st.k === "const" || st.k === "effect") {
          tail = {
            k: "letBody",
            pos: st.pos,
            name: st.k === "const" ? st.name : "",
            annot: st.k === "const" ? st.annot : null,
            init: st.k === "const" ? st.init : st.e,
            body: tail,
          };
        } else
          this.fail(
            at,
            "statements after an unconditional return are outside the closure slice",
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

  block(node: any): Stmt[] {
    if (node.kind !== ts.SyntaxKind.Block) this.fail(node, "expected a block");
    return node.statements.map((s: any) => this.stmt(s));
  }

  stmt(node: any): Stmt {
    switch (node.kind) {
      case ts.SyntaxKind.ExpressionStatement:
        return {
          k: "effect",
          pos: this.span(node),
          e: this.expr(node.expression),
        };

      case ts.SyntaxKind.ReturnStatement:
        if (!node.expression)
          this.fail(node, "a bare `return` is outside the fragment");
        return {
          k: "return",
          pos: this.span(node),
          e: this.expr(node.expression),
        };

      case ts.SyntaxKind.VariableStatement: {
        const list = node.declarationList;
        if (!(list.flags & ts.NodeFlags.Const))
          this.fail(node, "only `const` bindings are in the fragment");
        if (list.declarations.length !== 1)
          this.fail(node, "one binding per `const` in the fragment");
        const d = list.declarations[0];
        if (d.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(d, "destructuring is outside the fragment");
        if (d.name.text === "undefined")
          this.fail(d, "shadowing undefined is outside the fragment");
        if (!d.initializer) this.fail(d, "a `const` needs an initializer");
        return {
          k: "const",
          pos: this.span(node),
          name: d.name.text,
          namePos: this.span(d.name),
          annot: d.type ? this.typeOf(d.type) : null,
          init: this.expr(d.initializer),
        };
      }

      case ts.SyntaxKind.BreakStatement:
      case ts.SyntaxKind.ContinueStatement: {
        if (node.label)
          this.fail(node, "only unlabeled loop transfers are supported");
        // The nearest enclosing loop, not crossing into another function.
        let parent = node.parent;
        while (
          parent &&
          !isFunctionLike(parent) &&
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

      case ts.SyntaxKind.WhileStatement:
        return {
          k: "while",
          pos: this.span(node),
          cond: this.expr(node.expression),
          body: this.block(node.statement),
        };

      case ts.SyntaxKind.IfStatement:
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

      default:
        this.fail(
          node,
          `statement outside the fragment (${ts.SyntaxKind[node.kind]})`,
        );
    }
  }

  /* --------------------------------------------------------- functions -- */

  functionDecl(node: any): FunctionAst {
    if (!node.name) this.fail(node, "anonymous function");
    if (node.name.text === "undefined")
      this.fail(node, "shadowing undefined is outside the fragment");
    if (node.typeParameters?.length)
      this.fail(node, "generics are outside the fragment");
    if (node.modifiers?.length)
      this.fail(
        node,
        "modifiers (export/async/declare) are outside the fragment",
      );
    if (!node.body) this.fail(node, "a function must have a body");
    const params = node.parameters.map((p: any) => {
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
      params,
      retType: this.typeOf(node.type),
      body: this.block(node.body),
    };
  }
}

/* ------------------------------------------------------------- parsing -- */

/**
 * The whole file, or a gate rejection. A rejection is an Error whose message
 * begins "gate: ", which is what the command writes to stderr, so a caller and
 * the command report one wording.
 */
export function parseFile(file: string): Ast {
  const absolute = resolve(file);
  const text = readFileSync(absolute, "utf8");
  const source = openFile(absolute, text);
  const gate = new Gate(source);
  const functions = source.statements.map((s: any) => {
    if (s.kind !== ts.SyntaxKind.FunctionDeclaration)
      gate.fail(
        s,
        `top-level statement outside the fragment (${ts.SyntaxKind[s.kind]})`,
      );
    return gate.functionDecl(s);
  });
  if (functions.length === 0) gate.fail(null, "no functions in file");
  return {
    file,
    sourceSha256: createHash("sha256").update(text).digest("hex"),
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
  for (const statement of source.statements as readonly any[])
    if (
      statement.kind === ts.SyntaxKind.FunctionDeclaration &&
      statement.name &&
      statement.body
    )
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
export function typeOf(node: any): WireType {
  return new Gate(node.getSourceFile()).typeOf(node);
}

/* ---------------------------------------------------------------- main -- */

// Run as a command, or lend the type translation to another trusted tool. The
// annotation encoding must have exactly one implementation: a second one would
// be a second opinion about what a source type means.
if (process.argv[1] && import.meta.filename === resolve(process.argv[1])) {
  const file = process.argv[2];
  if (!file) {
    process.stderr.write("usage: parse-source.ts <file.ts>\n");
    process.exit(2);
  }
  try {
    process.stdout.write(JSON.stringify(parseFile(file), null, 1));
    close();
  } catch (error) {
    process.stderr.write(String((error as Error).message ?? error) + "\n");
    process.exit(1);
  }
}
