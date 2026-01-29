/**
 * AST inspection helpers for the reactivity analyzer.
 *
 * Provides generic iteration and small structural helpers.
 */

import ts from "typescript";
import type { Violation } from "./checker.js";

export type AnalyzerContext<TReport> = {
  ts: typeof import("typescript");
  typeChecker: ts.TypeChecker;
  sourceFile: ts.SourceFile;
  report: TReport;
  violations: Violation[];
};

export type NodePredicate<T extends ts.Node> = (node: ts.Node) => node is T;

/**
 * Handler for AST nodes. Returns violations found at this node.
 * Return an empty array or undefined if no violations.
 */
export type NodeHandler<TReport, TNode extends ts.Node> = (
  node: TNode,
  ctx: AnalyzerContext<TReport>,
) => Violation[] | void;

export type NodeIterator<TReport> = {
  /** Register a handler for nodes matching the predicate. */
  on: <TNode extends ts.Node>(predicate: NodePredicate<TNode>, handler: NodeHandler<TReport, TNode>) => void;
  /** Run the iterator, visiting all nodes and collecting violations from handlers. */
  run: () => Violation[];
};

export function createNodeIterator<TReport>(ctx: AnalyzerContext<TReport>): NodeIterator<TReport> {
  const handlers: Array<{
    predicate: (node: ts.Node) => boolean;
    handler: (node: ts.Node, ctx: AnalyzerContext<TReport>) => Violation[] | void;
  }> = [];

  const on = <TNode extends ts.Node>(
    predicate: NodePredicate<TNode>,
    handler: NodeHandler<TReport, TNode>,
  ): void => {
    handlers.push({
      predicate: predicate as (node: ts.Node) => boolean,
      handler: handler as (node: ts.Node, ctx: AnalyzerContext<TReport>) => Violation[] | void,
    });
  };

  const run = (): Violation[] => {
    const { ts: tsMod } = ctx;
    const violations: Violation[] = [];

    const visit = (node: ts.Node): void => {
      for (const h of handlers) {
        if (h.predicate(node)) {
          const result = h.handler(node, ctx);
          if (result) {
            violations.push(...result);
          }
        }
      }
      tsMod.forEachChild(node, visit);
    };

    visit(ctx.sourceFile);
    return violations;
  };

  return { on, run };
}

export function getImplementsNames(
  tsMod: typeof import("typescript"),
  heritageClauses: ts.NodeArray<ts.HeritageClause> | undefined,
): string[] {
  if (!heritageClauses) return [];
  const out: string[] = [];
  for (const hc of heritageClauses) {
    if (hc.token !== tsMod.SyntaxKind.ImplementsKeyword) continue;
    for (const t of hc.types) out.push(t.expression.getText());
  }
  return out;
}

export type LineCol = { line: number; col: number };

export type PropertyAccessInfo = {
  root: string;
  chain: string[];
  text: string;
  pos: LineCol;
};

export type PropertyAccessHit = {
  info: PropertyAccessInfo;
  lhs: ts.Expression;
};

export type IdentifierUse = {
  id: ts.Identifier;
  pos: LineCol;
  text: string;
  parent: ts.Node | undefined;
};

export function getTypeReferenceArgs(
  tsMod: typeof import("typescript"),
  typeChecker: ts.TypeChecker,
  type: ts.Type,
  typeName: string,
): readonly ts.Type[] | undefined {
  if (!(type.flags & tsMod.TypeFlags.Object)) return undefined;
  const obj = type as ts.ObjectType;
  const isRef = (obj.objectFlags & tsMod.ObjectFlags.Reference) !== 0;
  if (!isRef) return undefined;
  const ref = obj as ts.TypeReference;
  const symbolName = ref.target.symbol?.getName();
  if (symbolName !== typeName) return undefined;
  const args = typeChecker.getTypeArguments(ref);
  return args;
}

export function getTypePropertyNames(type: ts.Type): string[] {
  return type.getProperties().map((prop) => prop.getName());
}

export function getLineCol(sourceFile: ts.SourceFile, pos: number): LineCol {
  const lc = sourceFile.getLineAndCharacterOfPosition(pos);
  return { line: lc.line + 1, col: lc.character + 1 };
}

export function withEndCol(
  pos: { line: number; col: number },
  text: string,
): { line: number; col: number; endCol: number } {
  const len = Math.max(1, text.length);
  return { line: pos.line, col: pos.col, endCol: pos.col + len };
}

export function findMethodBody(
  tsMod: typeof import("typescript"),
  cls: ts.ClassDeclaration,
  name: string,
): ts.Block | undefined {
  for (const member of cls.members) {
    if (!tsMod.isMethodDeclaration(member)) continue;
    if (!member.name || !tsMod.isIdentifier(member.name)) continue;
    if (member.name.text !== name) continue;
    return member.body ?? undefined;
  }
  return undefined;
}

export function extractPropertyAccesses(
  tsMod: typeof import("typescript"),
  sourceFile: ts.SourceFile,
  node: ts.Node,
): PropertyAccessHit[] {
  const results: PropertyAccessHit[] = [];

  function visit(n: ts.Node): void {
    if (tsMod.isPropertyAccessExpression(n)) {
      const chain: string[] = [];
      let root: string | null = null;

      let current: ts.Expression = n;
      while (tsMod.isPropertyAccessExpression(current)) {
        chain.unshift(current.name.text);
        current = current.expression;
      }
      if (tsMod.isIdentifier(current)) {
        root = current.text;
      } else {
        root = current.getText(sourceFile);
      }

      results.push({
        info: {
          root,
          chain,
          text: n.getText(sourceFile),
          pos: getLineCol(sourceFile, n.getStart(sourceFile)),
        },
        lhs: n.expression,
      });
    }
    tsMod.forEachChild(n, visit);
  }

  visit(node);
  return results;
}
export function collectIdentifierUses(
  tsMod: typeof import("typescript"),
  sourceFile: ts.SourceFile,
  node: ts.Node,
  name: string,
): IdentifierUse[] {
  const results: IdentifierUse[] = [];

  function visit(n: ts.Node): void {
    if (tsMod.isIdentifier(n) && n.text === name) {
      results.push({
        id: n,
        pos: getLineCol(sourceFile, n.getStart(sourceFile)),
        text: n.getText(sourceFile),
        parent: n.parent,
      });
    }
    tsMod.forEachChild(n, visit);
  }

  visit(node);
  return results;
}

export function isIdentifierPropertyCall(
  tsMod: typeof import("typescript"),
  id: ts.Identifier,
  propertyName: string,
): boolean {
  const parent = id.parent;
  if (!parent || !tsMod.isPropertyAccessExpression(parent)) return false;
  if (parent.expression !== id) return false;
  if (parent.name.text !== propertyName) return false;
  const call = parent.parent;
  if (!call || !tsMod.isCallExpression(call)) return false;
  return call.expression === parent;
}

// =============================================================================
// Ancestor inspection helpers
// =============================================================================

/**
 * Find the first ancestor matching a predicate.
 */
export function findAncestor<T extends ts.Node>(
  node: ts.Node,
  predicate: (n: ts.Node) => n is T,
): T | undefined {
  let current = node.parent;
  while (current) {
    if (predicate(current)) return current;
    current = current.parent;
  }
  return undefined;
}

/**
 * Check if node is the right-hand side of a binary expression with a given operator.
 */
export function isRhsOfBinaryOp(
  tsMod: typeof import("typescript"),
  node: ts.Node,
  operatorKind: ts.SyntaxKind,
): ts.BinaryExpression | undefined {
  const parent = node.parent;
  if (!parent || !tsMod.isBinaryExpression(parent)) return undefined;
  if (parent.operatorToken.kind !== operatorKind) return undefined;
  if (parent.right !== node) return undefined;
  return parent;
}

/**
 * Check if node is the outermost expression (not wrapped in another expression).
 * Returns true if the parent is a statement or declaration context.
 */
export function isOutermostExpression(
  tsMod: typeof import("typescript"),
  node: ts.Expression,
): boolean {
  const parent = node.parent;
  if (!parent) return true;
  // If parent is an expression statement, we're outermost
  if (tsMod.isExpressionStatement(parent)) return true;
  // If parent is a variable declaration initializer
  if (tsMod.isVariableDeclaration(parent) && parent.initializer === node) return true;
  // If parent is an assignment and we're the RHS
  if (tsMod.isBinaryExpression(parent) && parent.right === node) return true;
  return false;
}

/**
 * Get the containing statement for a node.
 */
export function getContainingStatement(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Statement | undefined {
  let current: ts.Node | undefined = node;
  while (current) {
    if (tsMod.isStatement(current)) return current;
    current = current.parent;
  }
  return undefined;
}

/**
 * Check if a statement is the first statement in a block.
 */
export function isFirstStatementInBlock(
  tsMod: typeof import("typescript"),
  stmt: ts.Statement,
): ts.Block | undefined {
  const parent = stmt.parent;
  if (!parent || !tsMod.isBlock(parent)) return undefined;
  if (parent.statements.length === 0) return undefined;
  if (parent.statements[0] !== stmt) return undefined;
  return parent;
}

/**
 * Check if a block is the body of a for statement.
 */
export function isForLoopBody(
  tsMod: typeof import("typescript"),
  block: ts.Block,
): ts.ForStatement | ts.ForOfStatement | ts.ForInStatement | undefined {
  const parent = block.parent;
  if (!parent) return undefined;
  if (tsMod.isForStatement(parent) && parent.statement === block) return parent;
  if (tsMod.isForOfStatement(parent) && parent.statement === block) return parent;
  if (tsMod.isForInStatement(parent) && parent.statement === block) return parent;
  return undefined;
}

/**
 * Check if a block is the "then" branch of an if statement.
 */
export function isIfStatementBody(
  tsMod: typeof import("typescript"),
  block: ts.Block,
): ts.IfStatement | undefined {
  const parent = block.parent;
  if (!parent) return undefined;
  if (tsMod.isIfStatement(parent) && parent.thenStatement === block) return parent;
  return undefined;
}
