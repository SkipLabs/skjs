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
  ClassDeclaration,
  BinaryExpression,
  Expression,
  FunctionDeclaration,
  FunctionExpression,
  Identifier,
  ImportDeclaration,
  InterfaceDeclaration,
  MethodDeclaration,
  Node,
  ParameterDeclaration,
  SourceFile,
  Statement,
  TypeAliasDeclaration,
  TypeParameterDeclaration,
  VariableStatement,
  TypeNode,
} from "typescript/unstable/ast";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import type { Atom } from "./claim.mts";
import type { DeclarationIdentity, TypeTerm } from "./declaration-types.mts";
import { optionalTerm, restPositions, REST_CONTRACT, typeTerm, type TermScope } from "./type-term.mts";
import type {
  Ast,
  BindingAst,
  Expr,
  FunctionAst,
  PatternPropAst,
  Stmt,
  TypeParamAst,
  ArithOp,
  ArrayElemAst,
  TypeofShape,
} from "./fragment.mts";
import type { Span } from "./span.mts";
import { messageOf } from "./thrown.mts";
import { collectDeclarations, DeclarationError, tsconfigOf } from "./declaration-graph.mts";
import { asyncCompleteName, asyncReturnName, awaitName } from "./intrinsics.mts";

/** A question-mark parameter requires an optional suffix. A default may
 * precede a required parameter: callers supply undefined in that position. */
function firstOptional(
  parameters: readonly { questionToken?: unknown; initializer?: unknown }[],
): number {
  const i = parameters.findIndex((p) => !!p.questionToken);
  return i < 0 ? parameters.length : i;
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
  const changed = opened.has(absolute);
  // The compiler keeps an open file's old text even when `fileChanges` names
  // it. Release that open document first, then reopen it from our current
  // snapshot bytes; otherwise a changed source can receive a stale tree.
  if (changed)
    compiler.updateSnapshot({ closeFiles: [absolute], fileChanges: { changed: [absolute] } });
  const snapshot = compiler.updateSnapshot({
    openFiles: [absolute],
    ...(changed ? { fileChanges: { changed: [absolute] } } : {}),
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

class Gate {
  // Written out rather than a parameter property: node strips types, it does
  // not compile them, so the syntax has to be erasable.
  private readonly file: SourceFile;
  /* Type-parameter names are resolved lexically. Keeping frames, rather than
   * one file-wide set, makes nested quantified callables representable without
   * conflating an inner binder with an outer binder of the same spelling. */
  private readonly typeParamScopes: Set<string>[] = [];
  /** Local spelling to the arity and identity of its declaration root. A
   * reference names the declaration TypeScript resolved the spelling to. */
  private readonly declaredTypes = new Map<string,
    { required: number; total: number; declaration: DeclarationIdentity }>();
  /* Whether the code being read is strict, by a module or a "use strict"
   * directive (ECMAScript's, not TypeScript's `strict` option). An ordinary
   * function records it: its receiver rule is the strict one. */
  strict = false;
  // Mode of the ordinary function that bound `this`, or no binding. A strict
  // arrow captures its creator's already-converted receiver; it cannot rebind it.
  private receiverMode: "strict" | "sloppy" | null = null;
  /* Whether the function whose body is being read is async: its returns
     settle the promise its call returned (`intrinsics.mts`). */
  private asyncBody = false;
  constructor(file: SourceFile) {
    this.file = file;
    this.scope = this.termScope();
  }

  /** The leading `"use strict"` directives of a directive prologue: whether
   * there is one, and how many statements the prologue's "use strict" members
   * occupy, which are dropped since they do nothing else. Another directive
   * stays an ordinary statement. */
  useStrict(statements: readonly Statement[]): {
    strict: boolean;
    skip: Set<Statement>;
  } {
    const skip = new Set<Statement>();
    for (const statement of statements) {
      if (
        !ts.isExpressionStatement(statement) ||
        !ts.isStringLiteral(statement.expression)
      )
        break;
      // The directive is the exact source text, without escapes.
      const raw = statement.expression.getText(this.file);
      if (raw === '"use strict"' || raw === "'use strict'") skip.add(statement);
    }
    return { strict: skip.size > 0, skip };
  }

  private hasTypeParam(name: string): boolean {
    return this.typeParamScopes.some((scope) => scope.has(name));
  }

  private enterTypeParams(
    parameters: readonly TypeParameterDeclaration[] | undefined,
  ): TypeParamAst[] {
    const local = new Set<string>();
    const result: TypeParamAst[] = [];
    this.typeParamScopes.unshift(local);
    try {
      for (const tp of parameters ?? []) {
        if (tp.defaultType)
          this.fail(tp, "type parameter defaults are outside the fragment");
        if (tp.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(tp, "expected a type-parameter name");
        if (local.has(tp.name.text)) this.fail(tp, "duplicate type parameter");
        let bound: TypeTerm | null = null;
        if (tp.constraint) {
          const earlier =
            ts.isTypeReferenceNode(tp.constraint) &&
            tp.constraint.typeName.kind === ts.SyntaxKind.Identifier &&
            !tp.constraint.typeArguments?.length &&
            this.hasTypeParam(tp.constraint.typeName.text);
          const declared =
            ts.isTypeReferenceNode(tp.constraint) &&
            tp.constraint.typeName.kind === ts.SyntaxKind.Identifier &&
            !tp.constraint.typeArguments?.length &&
            this.declaredTypes.get(tp.constraint.typeName.text)?.total === 0;
          if (tp.constraint.kind !== ts.SyntaxKind.BooleanKeyword && !earlier && !declared)
            this.fail(
              tp.constraint,
              "only `extends boolean`, an earlier type parameter, or a non-generic named type is in the fragment",
            );
          bound = this.typeOf(tp.constraint);
        }
        result.push({ name: tp.name.text, bound });
        local.add(tp.name.text);
      }
      return result;
    } catch (error) {
      this.typeParamScopes.shift();
      throw error;
    }
  }

  private leaveTypeParams(): void {
    if (!this.typeParamScopes.shift())
      throw new Error("internal: no type-parameter scope to leave");
  }

  /** A class declaration, in module initialization order: one constant per
   * method, holding a closure allocated once, whose receiver is the instance,
   * as every instance shares its prototype's method; then the class, holding
   * its constructor, which allocates an instance from the field initializers
   * and those methods. Within the fragment an instance's own fields and its
   * prototype's methods are indistinguishable. The class value is that
   * constructor as construct-only code: `new` runs it, a plain call cannot. */
  classStmt(node: ClassDeclaration): Stmt {
    const name = node.name;
    if (!name) return this.fail(node, "an anonymous class is outside the fragment");
    if (node.typeParameters?.length) this.fail(node, "a generic class is outside the fragment");
    if (node.heritageClauses?.some((c) => c.token === ts.SyntaxKind.ExtendsKeyword))
      this.fail(node, "class inheritance is outside the fragment");
    if (node.modifiers?.some((m) => m.kind !== ts.SyntaxKind.ExportKeyword))
      this.fail(node, "a class modifier outside the fragment");
    const declared = this.declaredTypes.get(name.text);
    if (!declared) return this.fail(node, "a class declaration has no instance type");
    const instance: TypeTerm = { k: "reference", reference: { name: name.text, span: this.span(name),
      arguments: [], target: declared.declaration }, args: [], span: this.span(name) };
    const outerStrict = this.strict;
    // A class body is strict code.
    this.strict = true;
    try {
      const methods: BindingAst[] = [];
      const fields: { name: string; e: Expr }[] = [];
      const constructors = node.members.filter(ts.isConstructorDeclaration);
      const constructor = constructors[0];
      if (constructors.length > 1) this.fail(node, "a class has one constructor");
      // Fields a constructor assigns: the uninitialized ones, each once, as
      // `this.f = e` statements whose values do not read `this`. The instance
      // is then complete before anything can observe it.
      const uninitialized = new Set(node.members.filter(ts.isPropertyDeclaration)
        .filter((m) => !m.initializer && ts.isIdentifier(m.name))
        .map((m) => (m.name as Identifier).text));
      const readsThis = (n: Node): boolean =>
        n.kind === ts.SyntaxKind.ThisKeyword ||
        (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !!n.forEachChild((c) => readsThis(c) || undefined));
      const params = constructor ? constructor.parameters.map((p) => {
        if (!ts.isIdentifier(p.name) || p.questionToken || p.dotDotDotToken || p.initializer)
          this.fail(p, "a constructor parameter must be plain and required");
        if (p.name.text === "undefined") this.fail(p, "shadowing undefined is outside the fragment");
        return { name: p.name.text, type: this.typeOf(p.type, p), pos: this.span(p.name),
          property: !!p.modifiers?.length };
      }) : [];
      for (const member of node.members) {
        if (ts.isSemicolonClassElement(member) || ts.isConstructorDeclaration(member)) continue;
        if (ts.isPropertyDeclaration(member)) {
          if (!ts.isIdentifier(member.name)) this.fail(member, "a class member needs a plain name");
          if (member.initializer) {
            if (readsThis(member.initializer)) this.fail(member, "a field initializer that reads `this` is outside the fragment");
            fields.push({ name: member.name.text, e: this.expr(member.initializer) });
          }
        } else if (ts.isMethodDeclaration(member)) {
          if (!ts.isIdentifier(member.name)) this.fail(member, "a class member needs a plain name");
          methods.push({ name: `${name.text}.${member.name.text}`, namePos: this.span(member.name),
            annot: null, init: this.lambda(member, instance) });
          fields.push({ name: member.name.text,
            e: { k: "id", pos: this.span(member.name), name: `${name.text}.${member.name.text}` } });
        } else this.fail(member, "a class member outside the fragment");
      }
      // Parameter properties, then the constructor's assignments, in order:
      // after the field initializers, as JavaScript runs them.
      for (const p of params)
        if (p.property) fields.push({ name: p.name, e: { k: "id", pos: p.pos, name: p.name } });
      const assigned = new Set<string>();
      for (const statement of constructor?.body?.statements ?? []) {
        const e = ts.isExpressionStatement(statement) ? statement.expression : undefined;
        const target = e && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
          ts.isPropertyAccessExpression(e.left) && e.left.expression.kind === ts.SyntaxKind.ThisKeyword &&
          ts.isIdentifier(e.left.name) ? e.left.name.text : undefined;
        if (!e || !ts.isBinaryExpression(e) || target === undefined)
          this.fail(statement, "a constructor statement other than `this.f = e` is outside the fragment");
        if (!uninitialized.has(target) || assigned.has(target))
          this.fail(statement, "a constructor assigns each uninitialized field once");
        if (readsThis(e.right)) this.fail(statement, "a constructor assignment that reads `this` is outside the fragment");
        assigned.add(target);
        fields.push({ name: target, e: this.expr(e.right) });
      }
      for (const f of uninitialized)
        if (!assigned.has(f)) this.fail(node, `field ${f} is never initialized`);
      // The class value is its constructor as construct-only code, which only
      // `new` runs.
      const lambda: Expr = { k: "ctor", pos: this.span(node), lambda: { k: "lambda", pos: this.span(node),
        typeParams: [], receiver: null, params: params.map((p) => ({ name: p.name, type: p.type })),
        result: instance, body: { k: "alloc", pos: this.span(name), fields } } };
      const type: TypeTerm = { k: "constructor", params: params.map((p) => p.type), rest: null, result: instance,
        span: this.span(name) };
      return { k: "const", pos: this.span(node),
        bindings: [...methods, { name: name.text, namePos: this.span(name), annot: type, init: lambda }] };
    } finally {
      this.strict = outerStrict;
    }
  }

  registerDeclaredType(name: string, required: number, total: number,
      declaration: DeclarationIdentity, node: Node): void {
    if (this.declaredTypes.has(name))
      this.fail(node, "duplicate type name");
    this.declaredTypes.set(name, { required, total, declaration });
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

  /* ------------------------------------------------------ async, await -- */
  // `async` and `await` are trusted steps, written as calls of intrinsics
  // (`intrinsics.mts`): the call is at `pos`, the intrinsic read at `at`.

  private intrinsic(name: string, pos: Span, at: Span, args: Expr[]): Expr {
    return { k: "apply", pos, callee: { k: "id", pos: at, name }, args };
  }

  /** `await e`: `%Await%(e)`, the intrinsic read at the keyword. Every span
   * an intrinsic call or read is given is a node or a token of the source. */
  private awaitExpr(node: ts.AwaitExpression): Expr {
    const start = node.getStart(this.file);
    return this.intrinsic(awaitName, this.span(node), [start, start + "await".length],
      [this.expr(node.expression)]);
  }

  /** An async body completes with `return %AsyncComplete%()`: the call spans
   * the block, the intrinsic and the statement its closing brace. Nothing is
   * added to a body that returns on every path. */
  private asyncCompletion(block: ts.Block, statements: Stmt[]): Stmt[] {
    const returns = (xs: Stmt[]): boolean => {
      const last = xs.at(-1);
      return last?.k === "return" ||
        (last?.k === "if" && last.else_ !== null && returns(last.then) && returns(last.else_));
    };
    if (returns(statements)) return statements;
    const brace: Span = [block.end - 1, block.end];
    return [...statements, { k: "return", pos: brace,
      e: this.intrinsic(asyncCompleteName, this.span(block), brace, []) }];
  }

  text(node: Node): string {
    return this.file.text.slice(node.getStart(this.file), node.end);
  }

  /* ------------------------------------------------------------- types -- */

  /** Type syntax reads through the one source-term reader. A name is a
   * binder of an enclosing function or a declaration root; every declaration
   * root was resolved by TypeScript's checker. */
  private readonly scope: TermScope;
  private termScope(): TermScope {
    return {
      source: this.file,
      annotation: true,
      fail: (node, message) => this.fail(node, message),
      named: (node, span, read) => {
        const name = (node.typeName as Identifier).text;
        const declared = this.declaredTypes.get(name);
        if (declared !== undefined && !this.hasTypeParam(name)) {
          const args = node.typeArguments ?? [];
          if (args.length < declared.required || args.length > declared.total) {
            const count = declared.required === declared.total
              ? `${declared.total}`
              : `${declared.required} to ${declared.total}`;
            this.fail(node, `type '${name}' needs ${count} type argument(s)`);
          }
          return { k: "reference", reference: { name, span,
            arguments: args.map(arg => this.span(arg)), target: declared.declaration },
            args: args.map(read), span };
        }
        if (node.typeArguments?.length) this.fail(node, "unknown type alias");
        if (!this.hasTypeParam(name)) this.fail(node, "unknown type parameter");
        return { k: "binder", name, span };
      },
    };
  }

  typeOf(node: TypeNode | undefined, at: Node | null = null): TypeTerm {
    return typeTerm(this.scope, node, at);
  }

  /** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
   * value bound when a call omits that position. The fragment carries the
   * union, so nothing downstream needs a second representation of optionality.
   * A call may omit a trailing position exactly when its contract admits
   * `undefined`; declared arity is not observable in this fragment. */
  optionalTypeOf(node: TypeNode | undefined, at: Node): TypeTerm {
    return optionalTerm(this.typeOf(node, at), this.span(at));
  }

  /** A rest parameter's contract: its tuple of required positions or its
   * mutable array. */
  restType(p: ParameterDeclaration): TypeTerm {
    const type = this.typeOf(p.type, p);
    if (!restPositions(type)) this.fail(p, REST_CONTRACT);
    return type;
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

    if (ts.isAwaitExpression(node)) return this.awaitExpr(node);

    if (ts.isIdentifier(node)) {
      if (node.text === "undefined")
        return { k: "lit", pos: this.span(node), lit: { a: "undefined" } };
      // A class is a value like any other: its construct-only code is what a
      // plain call cannot run, which its type records.
      return { k: "id", pos: this.span(node), name: node.text };
    }

    if (ts.isNewExpression(node)) {
      // Explicit type arguments only constrain TypeScript: the instantiation a
      // producer claims is validated like any other. The callee is any value;
      // its type decides whether it has construct-only code.
      return {
        k: "new",
        pos: this.span(node),
        callee: this.expr(node.expression),
        args: (node.arguments ?? []).map((arg) => {
          if (ts.isSpreadElement(arg)) this.fail(arg, "a spread argument to `new` is outside the fragment");
          return this.expr(arg);
        }),
      };
    }

    if (node.kind === ts.SyntaxKind.ThisKeyword) {
      // Only an ordinary function expression, a method, or a declaration
      // stating a `this` parameter binds a receiver.
      if (this.receiverMode === null)
        this.fail(node, "`this` where no receiver is bound");
      // Check every source read here, including declaration bodies and lexical
      // captures. The calculus has no sloppy receiver conversion; checking only
      // lambda construction leaves declaration entry points unprotected.
      if (this.receiverMode === "sloppy")
        this.fail(node, "a function that reads `this` must be strict code");
      return { k: "this", pos: this.span(node) };
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

    if (
      ts.isPrefixUnaryExpression(node) &&
      node.operator === ts.SyntaxKind.MinusToken &&
      ts.isNumericLiteral(node.operand)
    ) {
      if (!DECIMAL.test(node.operand.text))
        this.fail(node, "non-decimal numeric literal");
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: "-" + node.operand.text },
      };
    }

    if (ts.isNumericLiteral(node)) {
      if (!DECIMAL.test(node.text))
        this.fail(node, "non-decimal numeric literal");
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: node.text },
      };
    }

    if (ts.isArrowFunction(node) || ts.isFunctionExpression(node))
      return this.lambda(node);

    if (ts.isObjectLiteralExpression(node)) {
      if (!node.properties.length)
        this.fail(node, "a record with no field has no location");
      const seen = new Set<string>();
      const fields = node.properties.map((f) => {
        // A method is an ordinary function expression in a field: it has no
        // `super` or construction here, which is all that tells them apart.
        if (ts.isMethodDeclaration(f) && ts.isIdentifier(f.name)) {
          const name = f.name.text;
          if (seen.has(name)) this.fail(f, "duplicate field name in a record");
          if (name === "__proto__")
            this.fail(f, "prototype initializers are outside the fragment");
          seen.add(name);
          return { name, e: this.lambda(f) };
        }
        // `{ x }` is `{ x: x }`: the name is read where it is written.
        if (ts.isShorthandPropertyAssignment(f) && !f.objectAssignmentInitializer &&
            ts.isIdentifier(f.name)) {
          const name = f.name.text;
          if (seen.has(name)) this.fail(f, "duplicate field name in a record");
          if (name === "__proto__")
            this.fail(f, "a `__proto__` field is outside the fragment");
          seen.add(name);
          return { name, e: this.expr(f.name) };
        }
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

    if (ts.isArrayLiteralExpression(node)) {
      if (
        node.elements.some(
          (e) => ts.isSpreadElement(e) || ts.isOmittedExpression(e),
        )
      )
        this.fail(
          node,
          "array literal spreads and holes are outside the fragment",
        );
      return {
        k: "arrayLit",
        pos: this.span(node),
        elems: node.elements.map((e) => this.expr(e)),
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
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        ts.isIdentifier(node.expression.expression) &&
        node.expression.expression.text === "Object" &&
        node.expression.name.text === "assign"
      ) {
        if (
          node.questionDotToken ||
          node.expression.questionDotToken ||
          node.typeArguments?.length !== 2 ||
          node.arguments.length !== 2 ||
          !ts.isArrowFunction(node.arguments[0]) ||
          !ts.isObjectLiteralExpression(node.arguments[1])
        )
          this.fail(
            node,
            "Object.assign requires a fresh arrow, an object literal and two explicit type arguments",
          );
        // The fragment cannot assign to Object.assign or pass Object as a value.
        // Reject any local declaration that could shadow the standard builtin.
        const checkBinding = (n: Node): void => {
          if (
            (ts.isParameterDeclaration(n) ||
              ts.isVariableDeclaration(n) ||
              ts.isFunctionDeclaration(n)) &&
            n.name &&
            ts.isIdentifier(n.name) &&
            n.name.text === "Object"
          )
            this.fail(
              n,
              "shadowing Object is outside intrinsic callable initialization",
            );
          n.forEachChild(checkBinding);
        };
        checkBinding(this.file);
        // These names either replace an intrinsic used by the lowering or
        // encounter special/non-writable properties on JavaScript functions.
        for (const property of node.arguments[1].properties) {
          if (
            ts.isPropertyAssignment(property) &&
            ts.isIdentifier(property.name) &&
            [
              "call",
              "bind",
              "apply",
              "name",
              "length",
              "caller",
              "arguments",
              "__proto__",
            ].includes(property.name.text)
          )
            this.fail(
              property,
              "special function properties are outside callable initialization",
            );
        }
        return {
          k: "withValue",
          pos: this.span(node),
          fn: this.expr(node.arguments[0]),
          initial: this.expr(node.arguments[1]),
          functionType: this.typeOf(node.typeArguments[0]),
          bagType: this.typeOf(node.typeArguments[1]),
        };
      }
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        node.expression.name.text === "apply"
      ) {
        // Function.prototype.apply reads its list as an array-like: its
        // length, then each index in order. It never iterates the list.
        if (
          node.questionDotToken ||
          node.expression.questionDotToken ||
          node.typeArguments?.length ||
          node.arguments.length === 0 ||
          node.arguments.length > 2 ||
          node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
          !this.localArrow(node.expression.expression)
        )
          this.fail(
            node,
            ".apply requires a known local function, an explicit receiver and at most one argument list",
          );
        const list = node.arguments[1];
        return {
          k: "applyWithReceiver",
          pos: this.span(node),
          callee: this.expr(node.expression.expression),
          receiver: this.expr(node.arguments[0]),
          list: list ? this.expr(list) : null,
        };
      }
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        ["call", "bind"].includes(node.expression.name.text)
      ) {
        if (
          node.questionDotToken ||
          node.expression.questionDotToken ||
          node.typeArguments?.length ||
          node.arguments.length === 0 ||
          node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
          !this.localArrow(node.expression.expression)
        )
          this.fail(
            node,
            `.${node.expression.name.text} requires a known local function, an explicit receiver and ordinary arguments`,
          );
        return {
          k:
            node.expression.name.text === "bind"
              ? "bindWithReceiver"
              : "callWithReceiver",
          pos: this.span(node),
          callee: this.expr(node.expression.expression),
          receiver: this.expr(node.arguments[0]),
          args: node.arguments.slice(1).map((arg) => this.expr(arg)),
        };
      }
      if (node.questionDotToken)
        this.fail(node, "expected an ordinary call, not an optional one");
      // A property reference, parenthesized or not, is a call target that
      // keeps its object as the receiver (EvaluateCall). A copied method is a
      // value, and takes the `apply` form below.
      let target: Expression = node.expression;
      while (ts.isParenthesizedExpression(target)) target = target.expression;
      if (
        ts.isPropertyAccessExpression(target) ||
        ts.isElementAccessExpression(target)
      ) {
        const spreads: number[] = [];
        const args = node.arguments.map((arg, i) => {
          if (!ts.isSpreadElement(arg)) return this.expr(arg);
          spreads.push(i);
          return this.expr(arg.expression);
        });
        // Explicit type arguments instantiate the method's leading binders;
        // Lean checks the claimed instance against them.
        const typeArgs = node.typeArguments?.map((t) => this.typeOf(t, node));
        return {
          k: "invoke",
          pos: this.span(node),
          callee: this.expr(node.expression),
          args,
          ...(spreads.length ? { spreads } : {}),
          ...(typeArgs?.length ? { typeArgs } : {}),
        };
      }
      // A spread writes the elements of one array in place of several
      // arguments, read where it is written: after every argument before it
      // and before every one after it. What it stands for — a tuple's
      // required positions, or elements a variadic callee collects — the
      // checker reads from the claims.
      if (node.typeArguments?.length)
        this.fail(node, "explicit type arguments are admitted on a method call only");
      const spreads: number[] = [];
      const args = node.arguments.map((arg, i) => {
        if (!ts.isSpreadElement(arg)) return this.expr(arg);
        spreads.push(i);
        return this.expr(arg.expression);
      });
      return {
        k: "apply",
        pos: this.span(node),
        callee: this.expr(node.expression),
        args,
        ...(spreads.length ? { spreads } : {}),
      };
    }

    this.fail(
      node,
      `expression outside the fragment (${ts.SyntaxKind[node.kind]})`,
    );
  }

  // A call signature alone does not establish the inherited .call intrinsic.
  // Follow immutable lexical aliases to source-created functions, and to a
  // function-valued member of a `const` object literal whose member no write
  // in the file can replace. Parameters and arbitrary call results may carry
  // their own .call property, so are refused.
  private localArrow(node: Expression, seen = new Set<number>()): boolean {
    if (ts.isParenthesizedExpression(node))
      return this.localArrow(node.expression, seen);
    if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return true;
    if (
      ts.isPropertyAccessExpression(node) &&
      !node.questionDotToken &&
      ts.isIdentifier(node.expression)
    ) {
      const member = node.name.text;
      const literal = this.constInitializer(node.expression, seen);
      if (!literal || !ts.isObjectLiteralExpression(literal)) return false;
      if (this.memberMayBeWritten(member)) return false;
      return literal.properties.some(
        (p) =>
          (ts.isMethodDeclaration(p) &&
            ts.isIdentifier(p.name) &&
            p.name.text === member) ||
          (ts.isPropertyAssignment(p) &&
            ts.isIdentifier(p.name) &&
            p.name.text === member &&
            (ts.isArrowFunction(p.initializer) ||
              ts.isFunctionExpression(p.initializer))),
      );
    }
    if (
      ts.isCallExpression(node) &&
      ts.isPropertyAccessExpression(node.expression) &&
      ts.isIdentifier(node.expression.expression) &&
      node.expression.expression.text === "Object" &&
      node.expression.name.text === "assign"
    )
      // Its initializer is separately parsed through the full Object.assign
      // gate. Do not parse it again here: its body may refer back to this name.
      return (
        node.arguments.length === 2 &&
        ts.isArrowFunction(node.arguments[0]) &&
        ts.isObjectLiteralExpression(node.arguments[1])
      );
    if (
      ts.isCallExpression(node) &&
      ts.isPropertyAccessExpression(node.expression) &&
      node.expression.name.text === "bind"
    )
      return this.localArrow(node.expression.expression, seen);
    if (!ts.isIdentifier(node)) return false;
    const init = this.constInitializer(node, seen);
    return !!init && this.localArrow(init, seen);
  }

  /** Whether any assignment in the file may replace a member of this name: a
   * write to it by name, or to a computed key that is not another name. */
  private memberMayBeWritten(member: string): boolean {
    let found = false;
    const visit = (n: Node): void => {
      if (found) return;
      if (
        ts.isBinaryExpression(n) &&
        n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment
      ) {
        let target: Expression = n.left;
        while (ts.isParenthesizedExpression(target)) target = target.expression;
        if (
          ts.isPropertyAccessExpression(target) &&
          target.name.text === member
        )
          found = true;
        if (
          ts.isElementAccessExpression(target) &&
          !(
            ts.isStringLiteral(target.argumentExpression) &&
            target.argumentExpression.text !== member
          )
        )
          found = true;
      }
      n.forEachChild(visit);
    };
    visit(this.file);
    return found;
  }

  /** The initializer of the `const` this identifier names, lexically, or
   * none where it names a parameter, a mutable local or nothing here. */
  private constInitializer(
    node: Identifier,
    seen: Set<number>,
  ): Expression | undefined {
    // Held as a string: a narrowing of `node` does not reach into a closure.
    const name = node.text;
    for (let scope = node.parent; scope; scope = scope.parent) {
      if (ts.isBlock(scope)) {
        for (const statement of scope.statements) {
          if (!ts.isVariableStatement(statement)) continue;
          for (const decl of statement.declarationList.declarations) {
            if (!ts.isIdentifier(decl.name) || decl.name.text !== name)
              continue;
            if (
              !(statement.declarationList.flags & ts.NodeFlags.Const) ||
              !decl.initializer ||
              seen.has(decl.getStart(this.file))
            )
              return undefined;
            seen.add(decl.getStart(this.file));
            return decl.initializer;
          }
        }
      }
      if (
        ts.isFunctionLikeDeclaration(scope) &&
        scope.parameters?.some(
          (p) => ts.isIdentifier(p.name) && p.name.text === name,
        )
      )
        return undefined;
    }
    return undefined;
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
    if (!op)
      this.fail(
        node,
        `binary operator outside the fragment (${ts.tokenToString(token)})`,
      );
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
        return this.update(
          node,
          node.left,
          node.operatorToken.kind,
          node.right,
          false,
        );
    }
    const arithmetic: Record<number, ArithOp> = {
      [ts.SyntaxKind.PlusToken]: "add",
      [ts.SyntaxKind.MinusToken]: "sub",
      [ts.SyntaxKind.AsteriskToken]: "mul",
      [ts.SyntaxKind.SlashToken]: "div",
    };
    const arith = arithmetic[node.operatorToken.kind];
    if (arith)
      return {
        k: "arith",
        pos: this.span(node),
        op: arith,
        l: this.expr(node.left),
        r: this.expr(node.right),
      };
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
      return {
        k: "logicalAssign",
        pos: this.span(node),
        op: logicalOp,
        target,
        rhs: this.expr(node.right),
      };
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
    if (
      node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
      ts.isArrayLiteralExpression(node.left)
    ) {
      // `[a, b = d] = rhs`: each element names a mutable local, with a
      // default written as an assignment inside the literal.
      const names = new Set<string>();
      const targets: ArrayElemAst[] = node.left.elements.map((el, index) => {
        const target =
          ts.isBinaryExpression(el) &&
          el.operatorToken.kind === ts.SyntaxKind.EqualsToken
            ? el.left
            : el;
        const dflt =
          ts.isBinaryExpression(el) &&
          el.operatorToken.kind === ts.SyntaxKind.EqualsToken
            ? el.right
            : null;
        if (ts.isSpreadElement(el) || ts.isOmittedExpression(el))
          this.fail(el, "rest elements are outside the fragment");
        if (!ts.isIdentifier(target))
          this.fail(el, "only field and local assignments are supported");
        if (target.text === "undefined")
          this.fail(el, "shadowing undefined is outside the fragment");
        if (names.has(target.text)) this.fail(el, "duplicate pattern binding");
        names.add(target.text);
        return {
          index,
          name: target.text,
          namePos: this.span(target),
          default_: dflt ? this.expr(dflt) : null,
        };
      });
      return {
        k: "arrayAssign",
        pos: this.span(node),
        targets,
        rhs: this.expr(node.right),
      };
    }
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
      if (
        ts.isElementAccessExpression(node.left) &&
        !node.left.questionDotToken
      )
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
          : this.fail(
              node.left,
              "only field and local assignments are supported",
            ),
        receiver: this.expr(
          ts.isPropertyAccessExpression(node.left)
            ? node.left.expression
            : this.fail(
                node.left,
                "only field and local assignments are supported",
              ),
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
      const unwrap = (e: Expression): Expression =>
        ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e;
      const left = unwrap(node.left),
        right = unwrap(node.right);
      const shapes: readonly TypeofShape[] = ["number", "string", "boolean", "undefined", "function", "bigint", "symbol"];
      const shapeOf = (e: Expression): TypeofShape | undefined =>
        ts.isStringLiteral(e) ? shapes.find((s) => s === e.text) : undefined;
      const pair =
        ts.isTypeOfExpression(left) && shapeOf(right)
          ? { operand: left, shape: shapeOf(right) }
          : ts.isTypeOfExpression(right) && shapeOf(left)
            ? { operand: right, shape: shapeOf(left) }
            : null;
      if (pair?.shape)
        return {
          k: "typeofTest",
          pos: this.span(node),
          shape: pair.shape,
          equal: op === "===",
          e: this.expr(pair.operand.expression),
        };
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

  private lambda(
    node: ArrowFunction | FunctionExpression | MethodDeclaration,
    instance?: TypeTerm,
  ): Expr {
    const isAsync = node.modifiers?.length === 1 &&
      node.modifiers[0]?.kind === ts.SyntaxKind.AsyncKeyword;
    if (node.modifiers?.length && !isAsync)
      this.fail(node, "expected a closure without modifiers other than `async`");
    const ordinary = !ts.isArrowFunction(node);
    if (!ts.isArrowFunction(node)) {
      if (node.asteriskToken)
        this.fail(node, "generator functions are outside the fragment");
      // A named function expression binds its own name inside itself. A name
      // the function never refers to binds nothing it reads; one it does refer
      // to is a recursive binding, which the fragment has no frame for, as for
      // a cyclic closure initialization.
      if (ts.isFunctionExpression(node) && node.name) {
        const own = node.name.text;
        let uses = false;
        const visit = (n: Node): void => {
          if (uses) return;
          if (ts.isPropertyAccessExpression(n)) {
            visit(n.expression);
            return;
          }
          if (ts.isIdentifier(n) && n.text === own) uses = true;
          n.forEachChild(visit);
        };
        node.parameters.forEach(visit);
        if (node.body) visit(node.body);
        if (uses)
          this.fail(
            node,
            "a function expression that refers to its own name is a recursive binding, outside the fragment",
          );
      }
      if (ts.isMethodDeclaration(node) && node.postfixToken)
        this.fail(
          node,
          "an optional or definite method is outside the fragment",
        );
    }
    // An ordinary function's leading `this: T` states its receiver; without
    // one, any receiver is accepted. An arrow cannot declare one.
    const head = node.parameters[0];
    const stated =
      !!head && ts.isIdentifier(head.name) && head.name.text === "this";
    if (stated && instance)
      this.fail(head, "a class method's receiver is its instance");
    if (stated && !ordinary)
      this.fail(head, "an arrow cannot declare a receiver");
    if (
      stated &&
      (!head.type ||
        head.questionToken ||
        head.dotDotDotToken ||
        head.initializer)
    )
      this.fail(head, "a receiver needs a required type annotation");
    const parameters = stated ? node.parameters.slice(1) : [...node.parameters];
    const body = node.body;
    if (!body) this.fail(node, "a function must have a body");
    // A directive prologue in the function's own body makes it strict. It
    // is a syntax error beside parameters that are not simple.
    const prologue = ts.isBlock(body)
      ? this.useStrict(body.statements)
      : { strict: false, skip: new Set<Statement>() };
    if (
      prologue.strict &&
      parameters.some((p) => p.initializer || p.dotDotDotToken)
    )
      this.fail(node, '"use strict" beside non-simple parameters');
    const outerStrict = this.strict;
    const outerReceiverMode = this.receiverMode;
    const outerAsync = this.asyncBody;
    this.strict = outerStrict || prologue.strict;
    if (ordinary) {
      this.receiverMode = this.strict ? "strict" : "sloppy";
    }
    const typeParams = this.enterTypeParams(node.typeParameters);
    try {
      this.asyncBody = isAsync;
      const receiver = !ordinary
        ? null
        : {
            // A class method's receiver is its instance.
            type: instance ? instance : stated
              ? this.typeOf(head.type, head)
              : ({ k: "atom", name: "unknown", span: this.span(node) } as TypeTerm),
            strict: this.strict,
          };
      // Each name is taken where its parameter has just been checked: a
      // narrowing does not survive into the second pass over the same list.
      const names = parameters.map((p) => {
        if (!ts.isIdentifier(p.name) || p.name.text === "this")
          this.fail(p, "expected an ordinary closure parameter");
        if (p.questionToken && p.initializer)
          this.fail(p, "a parameter cannot be both optional and defaulted");
        if (p.dotDotDotToken) {
          if (p.questionToken || p.initializer)
            this.fail(p, "a rest parameter is neither optional nor defaulted");
          if (p !== parameters[parameters.length - 1])
            this.fail(p, "a rest parameter must be the last one");
          this.restType(p);
        }
        if (
          !p.questionToken &&
          !p.initializer &&
          !p.dotDotDotToken &&
          parameters.indexOf(p) > firstOptional(parameters)
        )
          this.fail(p, "a required parameter cannot follow an optional one");
        if (p.name.text === "undefined")
          this.fail(p, "shadowing undefined is outside the fragment");
        return p.name.text;
      });

      // A closure without a result annotation leaves its result to the
      // producer: the claim at the closure states it, and the body is checked
      // against that claim. A class method's result is its instance type's
      // member, which states it, so a method still needs the annotation.
      const declaredResult: TypeTerm | null =
        node.type || instance ? this.typeOf(node.type, node) : null;
      const result = (): TypeTerm => declaredResult ??
        this.fail(node, "a closure returning from a branch needs a result annotation");
      // An async arrow's expression body is its return: `%AsyncReturn%(e)`,
      // the call at `=>`, the intrinsic read at `async`.
      const statements = (block: ts.Block): Stmt[] => {
        const stmts = block.statements
          .filter((s) => !prologue.skip.has(s))
          .map((s) => this.stmt(s));
        return isAsync ? this.asyncCompletion(block, stmts) : stmts;
      };
      const arrow = ts.isArrowFunction(node) ? this.span(node.equalsGreaterThanToken) : null;
      const keyword = node.modifiers?.[0];
      const lowered = ts.isBlock(body)
        ? this.closureBlock(body, statements(body), result)
        : isAsync && arrow && keyword
          ? this.intrinsic(asyncReturnName, arrow, this.span(keyword), [this.expr(body)])
          : this.expr(body);
      return {
        k: "lambda",
        pos: this.span(node),
        typeParams,
        receiver,
        params: parameters.map((p, i) => ({
          name: names[i],
          // A defaulted parameter's type is what the body reads; the default
          // itself is the expression that replaces an omitted argument. A rest
          // parameter's type is the tuple its arguments are collected into.
          type: p.questionToken
            ? this.optionalTypeOf(p.type, p)
            : this.typeOf(p.type, p),
          ...(p.initializer ? { default: this.expr(p.initializer) } : {}),
          ...(p.dotDotDotToken ? { rest: true as const } : {}),
        })),
        result: declaredResult,
        body: lowered,
      };
    } finally {
      this.leaveTypeParams();
      this.strict = outerStrict;
      this.receiverMode = outerReceiverMode;
      this.asyncBody = outerAsync;
    }
  }

  private closureBlock(
    at: Node,
    statements: Stmt[],
    result: () => TypeTerm,
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
        if (st.k === "while" || st.k === "forOf" || st.k === "break" || st.k === "continue")
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
              result: { k: "atom", name: "null", span: st.pos },
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
    if (ts.isArrayBindingPattern(pattern)) {
      if (d.type) this.fail(d, "an annotated pattern is outside the fragment");
      if (!d.initializer) this.fail(d, "a `const` needs an initializer");
      if (pattern.elements.length === 0)
        this.fail(pattern, "an empty pattern binds nothing");
      const names = new Set<string>();
      const elems: ArrayElemAst[] = pattern.elements.map((el, index) => {
        // A hole is an omitted expression, or a binding element without a name.
        if (ts.isOmittedExpression(el) || !el.name)
          this.fail(el, "array pattern holes are outside the fragment");
        if (el.dotDotDotToken)
          this.fail(el, "rest elements are outside the fragment");
        const name = el.name;
        if (!ts.isIdentifier(name))
          this.fail(el, "nested patterns are outside the fragment");
        if (name.text === "undefined")
          this.fail(el, "shadowing undefined is outside the fragment");
        if (names.has(name.text)) this.fail(el, "duplicate pattern binding");
        names.add(name.text);
        return {
          index,
          name: name.text,
          namePos: this.span(name),
          default_: el.initializer ? this.expr(el.initializer) : null,
        };
      });
      return {
        k: "arrayPattern",
        pos: this.span(node),
        elems,
        init: this.expr(d.initializer),
      };
    }
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
        this.fail(
          el,
          "computed or string pattern keys are outside the fragment",
        );
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
      const e = this.expr(node.expression);
      // In an async body, `return e` is `return %AsyncReturn%(e)`, the call
      // spanning the statement, the intrinsic read at the keyword.
      const start = node.getStart(this.file);
      return {
        k: "return",
        pos: this.span(node),
        e: this.asyncBody
          ? this.intrinsic(asyncReturnName, this.span(node), [start, start + "return".length], [e])
          : e,
      };
    }

    if (ts.isVariableStatement(node)) {
      const list = node.declarationList;
      const mutable = !(list.flags & ts.NodeFlags.Const);
      // `var` is function-scoped and hoisted, so it is not this binding form.
      if (mutable && !(list.flags & ts.NodeFlags.Let))
        this.fail(node, "`var` is outside the fragment");
      const kindWord = mutable ? "let" : "const";
      if (
        list.declarations.some(
          (d) =>
            ts.isObjectBindingPattern(d.name) ||
            ts.isArrayBindingPattern(d.name),
        )
      )
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
        !ts.isWhileStatement(parent) &&
        !ts.isForOfStatement(parent)
      )
        parent = parent.parent;
      if (!parent || !(ts.isWhileStatement(parent) || ts.isForOfStatement(parent)))
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

    // `for (const x of e) body`: one immutable binding per iteration. The
    // loop is over an array, which Lean checks: the iterable is the argument
    // of the intrinsic that steps its iterator (`intrinsics.mts`).
    if (ts.isForOfStatement(node)) {
      if (node.awaitModifier)
        this.fail(node, "`for await` is outside the fragment");
      const list = node.initializer;
      if (!ts.isVariableDeclarationList(list) || !(list.flags & ts.NodeFlags.Const) ||
          list.declarations.length !== 1)
        this.fail(node, "a `for...of` loop declares one `const` binding");
      const d = list.declarations[0];
      if (!ts.isIdentifier(d.name))
        this.fail(d, "destructuring is outside the fragment");
      if (d.type || d.initializer)
        this.fail(d, "a `for...of` binding takes the element's type");
      if (d.name.text === "undefined")
        this.fail(d, "shadowing undefined is outside the fragment");
      return {
        k: "forOf",
        pos: this.span(node),
        name: d.name.text,
        namePos: this.span(d.name),
        iterable: this.expr(node.expression),
        body: this.block(node.statement),
      };
    }

    if (ts.isIfStatement(node)) {
      if (node.elseStatement && node.elseStatement.kind !== ts.SyntaxKind.Block)
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

  /* --------------------------------------------------------- functions -- */

  functionDecl(node: FunctionDeclaration): FunctionAst {
    if (!node.name) this.fail(node, "anonymous function");
    if (node.name.text === "undefined")
      this.fail(node, "shadowing undefined is outside the fragment");
    if (node.modifiers?.some(modifier => modifier.kind !== ts.SyntaxKind.ExportKeyword &&
        modifier.kind !== ts.SyntaxKind.AsyncKeyword))
      this.fail(
        node,
        "only the export and async modifiers are admitted on a source function",
      );
    if (node.asteriskToken)
      this.fail(node, "generator functions are outside the fragment");
    const isAsync = !!node.modifiers?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword);
    if (!node.body) this.fail(node, "a function must have a body");
    const prologue = this.useStrict(node.body.statements);
    if (
      prologue.strict &&
      node.parameters.some((p) => p.initializer || p.dotDotDotToken)
    )
      this.fail(node, '"use strict" beside non-simple parameters');
    const outerStrict = this.strict;
    this.strict = outerStrict || prologue.strict;
    // A declaration is the entry point, not a callable of the fragment: a
    // `this: T` parameter is one more input assumed at its annotation, like
    // every other parameter, and the body's `this` is that parameter.
    const head = node.parameters[0];
    const receiverParam =
      !!head && ts.isIdentifier(head.name) && head.name.text === "this";
    if (
      receiverParam &&
      (!head.type || head.questionToken || head.dotDotDotToken)
    )
      this.fail(head, "a receiver needs a required type annotation");
    const outerReceiverMode = this.receiverMode;
    const outerAsync = this.asyncBody;
    this.receiverMode = receiverParam
      ? this.strict
        ? "strict"
        : "sloppy"
      : null;
    const typeParams = this.enterTypeParams(node.typeParameters);
    try {
      this.asyncBody = isAsync;
      const params = node.parameters.map((p) => {
        if (p.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(p, "destructuring parameter");
        if (p.name.text === "undefined")
          this.fail(p, "shadowing undefined is outside the fragment");
        if (
          !p.questionToken &&
          !p.dotDotDotToken &&
          node.parameters.indexOf(p) > firstOptional(node.parameters)
        )
          this.fail(p, "a required parameter cannot follow an optional one");
        if (p.dotDotDotToken) {
          if (p.questionToken) this.fail(p, "a rest parameter is not optional");
          if (p !== node.parameters[node.parameters.length - 1])
            this.fail(p, "a rest parameter must be the last one");
          this.restType(p);
        }
        if (p.initializer)
          this.fail(p, "default parameters are outside the fragment");
        return {
          name: p.name.text,
          pos: this.span(p.name),
          type: p.questionToken
            ? this.optionalTypeOf(p.type, p)
            : this.typeOf(p.type, p),
          ...(p.dotDotDotToken ? { rest: true as const } : {}),
        };
      });
      const body = node.body.statements
        .filter((s) => !prologue.skip.has(s))
        .map((s) => this.stmt(s));
      return {
        name: node.name.text,
        namePos: this.span(node.name),
        typeParams,
        params,
        retType: this.typeOf(node.type),
        body: isAsync ? this.asyncCompletion(node.body, body) : body,
      };
    } finally {
      this.leaveTypeParams();
      this.strict = outerStrict;
      this.receiverMode = outerReceiverMode;
      this.asyncBody = outerAsync;
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
export function parseFile(file: string, carriesContext = false,
  tsconfigPath?: string, resolutionFile = file): Ast {
  const absolute = resolve(file);
  const text = readFileSync(absolute, "utf8");
  const source = openFile(absolute, text);
  const gate = new Gate(source);
  const aliasNodes: TypeAliasDeclaration[] = [];
  const interfaceNodes: InterfaceDeclaration[] = [];
  const classNodes: ClassDeclaration[] = [];
  const fnNodes: FunctionDeclaration[] = [];
  const importNodes: ImportDeclaration[] = [];
  // Top-level code other than declarations: the module's initialization, run
  // once, in order, after its function declarations are instantiated.
  const initNodes: Statement[] = [];
  // A "use strict" directive prologue makes the whole file strict.
  const prologue = gate.useStrict(source.statements);
  gate.strict = prologue.strict;
  for (const s of source.statements) {
    if (prologue.skip.has(s)) continue;
    if (ts.isTypeAliasDeclaration(s)) aliasNodes.push(s);
    else if (ts.isInterfaceDeclaration(s) && !carriesContext) interfaceNodes.push(s);
    // A class declaration declares its instance type, and its value is part of
    // the module's initialization, in order: classes are not hoisted.
    else if (ts.isClassDeclaration(s) && !carriesContext) {
      classNodes.push(s);
      initNodes.push(s);
    }
    else if (ts.isFunctionDeclaration(s)) fnNodes.push(s);
    else if (ts.isImportDeclaration(s) && !carriesContext) importNodes.push(s);
    else if (carriesContext) continue;
    else if (ts.isExpressionStatement(s)) initNodes.push(s);
    else if (ts.isVariableStatement(s)) {
      // A module constant is read by functions at its annotation. Module
      // storage that functions could write is not yet in the fragment.
      if (!(s.declarationList.flags & ts.NodeFlags.Const))
        gate.fail(s, "a module-level `let` or `var` is outside the fragment");
      initNodes.push(s);
    }
    else
      gate.fail(
        s,
        `top-level statement outside the fragment (${ts.SyntaxKind[s.kind]})`,
      );
  }
  // Every module body is strict, including one whose only module syntax is a
  // type-only import. This decides the receiver rule for nested ordinary
  // functions when imported declarations become certifiable.
  gate.strict = prologue.strict || importNodes.length > 0 ||
    interfaceNodes.some(node => node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) ||
    fnNodes.some(fn => fn.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword));
  let declarations: Ast["declarations"] = { roots: [], definitions: [], values: [], symbols: [] };
  const statable = (node: TypeAliasDeclaration): boolean => {
    const params = node.typeParameters;
    return !node.modifiers?.length && params?.length === 1 &&
      !params[0].constraint && !params[0].defaultType;
  };
  const localNodes: Array<TypeAliasDeclaration | InterfaceDeclaration | ClassDeclaration> =
    [...(carriesContext ? aliasNodes.filter(statable) : aliasNodes), ...interfaceNodes, ...classNodes];
  // A type name the file neither imports nor declares may be a global, such
  // as the standard library's `Promise`: TypeScript decides, and a global
  // declaration joins the graph as a root. Each name's first reference
  // stands for it.
  const rooted = new Set<string>([
    ...importNodes.flatMap(node => {
      const bindings = node.importClause?.namedBindings;
      return bindings && ts.isNamedImports(bindings) ? bindings.elements.map(e => e.name.text) : [];
    }),
    ...[...aliasNodes, ...interfaceNodes, ...classNodes].flatMap(node => node.name ? [node.name.text] : []),
  ]);
  const globalNodes: Identifier[] = [];
  const findGlobals = (node: Node): void => {
    if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) &&
        !rooted.has(node.typeName.text) && !globalNodes.some(g => g.text === (node.typeName as Identifier).text))
      globalNodes.push(node.typeName);
    node.forEachChild(findGlobals);
  };
  if (!carriesContext) findGlobals(source);
  // An array reaches `Array.prototype`, whose contract then joins the graph;
  // the first array the file writes stands for it.
  let firstArray: Node | undefined;
  const findArray = (node: Node): void => {
    if (firstArray) return;
    if (ts.isArrayTypeNode(node) || ts.isTupleTypeNode(node) || ts.isArrayLiteralExpression(node) ||
        ts.isForOfStatement(node) || (ts.isParameterDeclaration(node) && !!node.dotDotDotToken)) {
      firstArray = node;
      return;
    }
    node.forEachChild(findArray);
  };
  findArray(source);
  // `async`, `await` and `for...of` are calls of intrinsics, which then join
  // the declarations; the first such construct stands for them.
  let firstAsync: Node | undefined;
  const findAsync = (node: Node): void => {
    if (firstAsync) return;
    if (ts.isAwaitExpression(node) || ts.isForOfStatement(node) || (ts.isFunctionLikeDeclaration(node) &&
        !!node.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword))) {
      firstAsync = node;
      return;
    }
    node.forEachChild(findAsync);
  };
  if (!carriesContext) findAsync(source);
  if (importNodes.length || localNodes.length || globalNodes.length || firstArray || firstAsync) {
    const first = importNodes[0] ?? localNodes[0] ?? globalNodes[0] ?? firstArray ?? firstAsync;
    if (!first) throw Error("missing declaration root");
    // Named imports only. A type import joins the declaration graph; a value
    // import is an assumption at the type its declaration states.
    for (const node of importNodes) {
      const clause = node.importClause;
      if (!clause || clause.name || !clause.namedBindings ||
          !ts.isNamedImports(clause.namedBindings))
        gate.fail(node, "only named imports are in the source fragment");
    }
    // TypeScript resolves every name, in the project that owns the file or the
    // one named explicitly: the declaration graph is the compiler's.
    try {
      declarations = collectDeclarations(resolutionFile, { tsconfigPath, client: source,
        locals: localNodes.map(node => gate.span(node)),
        globals: globalNodes.map(node => gate.span(node)),
        ...(firstArray ? { arrays: gate.span(firstArray) } : {}),
        ...(firstAsync ? { intrinsics: gate.span(firstAsync) } : {}) });
    } catch (error) {
      const at = error instanceof DeclarationError
        ? [...importNodes, ...localNodes, ...globalNodes, ...(firstArray ? [firstArray] : []),
            ...(firstAsync ? [firstAsync] : [])].find(node =>
            node.getStart(source) === error.at[0]) ?? first
        : first;
      gate.fail(at, messageOf(error));
    }
    for (const root of declarations.roots) {
      const identity = root.declaration;
      const definition = declarations.definitions.find(d =>
        d.declaration.module === identity.module && d.declaration.name === identity.name &&
        d.declaration.span[0] === identity.span[0] &&
        d.declaration.span[1] === identity.span[1]);
      if (!definition)
        return gate.fail(first, `type definition missing: ${identity.module}#${identity.name}`);
      const node = [...importNodes, ...localNodes, ...globalNodes].find(n =>
        n.getStart(source) === root.binding.span[0]) ?? first;
      gate.registerDeclaredType(root.binding.local,
        definition.parameters.filter(p => p.default === null).length,
        definition.parameters.length, identity, node);
    }
  }
  // Carried context skips aliases its old fragment could not state. Every
  // retained declaration now has one source equation, shared with imports.
  // A function without a body is a declaration, not an example of one.
  const declared = carriesContext ? fnNodes.filter((s) => s.body) : fnNodes;
  const functions = declared.map((s) => gate.functionDecl(s));
  const init = initNodes.map((s) => ts.isClassDeclaration(s) ? gate.classStmt(s) : gate.stmt(s));
  if (functions.length === 0 && init.length === 0) gate.fail(null, "no functions in file");
  return {
    file,
    sourceSha256: createHash("sha256").update(text).digest("hex"),
    declarations,
    functions,
    init,
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

/** Class bodies named for coverage accounting only. Discovering a callable
 * does not lower or certify it: `new`, initialization, and prototype method
 * lookup still need their own source and semantic rules. */
export function definedClassCallables(
  file: string,
): { name: string; namePos: Span }[] {
  const absolute = resolve(file);
  const source = projectFor(absolute).program.getSourceFile(absolute);
  if (!source) throw new Error(`the compiler produced no tree for ${file}`);
  const out: { name: string; namePos: Span }[] = [];
  for (const statement of source.statements) {
    if (!ts.isClassDeclaration(statement) || !statement.name) continue;
    for (const member of statement.members) {
      if (ts.isConstructorDeclaration(member) && member.body) {
        out.push({
          name: `${statement.name.text}.constructor`,
          namePos: [member.getStart(source), member.end],
        });
      } else if (ts.isMethodDeclaration(member) && member.body) {
        out.push({
          name: `${statement.name.text}.${member.name.getText(source)}`,
          namePos: [member.name.getStart(source), member.name.end],
        });
      }
    }
  }
  return out;
}

/**
 * The fragment's reading of one type annotation, for a trusted tool that has a
 * node and needs the type the gate would give it. The annotation's own file is
 * the place a rejection names, which is why the node carries it.
 */
export function typeOf(node: TypeNode): TypeTerm {
  return new Gate(node.getSourceFile()).typeOf(node);
}

/* ---------------------------------------------------------------- main -- */

// Run as a command, or lend the type translation to another trusted tool. The
// annotation encoding must have exactly one implementation: a second one would
// be a second opinion about what a source type means.
if (process.argv[1] && import.meta.filename === resolve(process.argv[1])) {
  const args = process.argv.slice(2);
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: fragment-parse.mts <file.ts> [--project tsconfig-or-directory]\n");
    process.exit(2);
  }
  try {
    process.stdout.write(JSON.stringify(parseFile(args[0], false,
      args[2] ? tsconfigOf(args[2]) : undefined), null, 1));
    close();
  } catch (error) {
    process.stderr.write(messageOf(error) + "\n");
    process.exitCode = 1;
  }
}
