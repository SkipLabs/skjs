/**
 * Guard analysis utilities for AST inspection.
 *
 * This module provides helpers for analyzing guarded code patterns like:
 * - Bound checks: `i < arr.length`
 * - Element access: `arr[i]`
 * - Guarded statements: for-loops and if-statements
 * - Safe evaluation positions: assignments, return statements, call arguments
 *
 * These utilities are useful for checkers that need to determine if code
 * is protected by runtime guards.
 */

import ts from "typescript";
import {
  isRhsOfBinaryOp,
  getContainingStatement,
  isFirstStatementInBlock,
  isForLoopBody,
  isIfStatementBody,
} from "./ast-inspection.js";

// =============================================================================
// Types
// =============================================================================

/**
 * Statements that guard their body with a condition.
 * - ForStatement: `for (init; condition; increment) { body }`
 * - IfStatement: `if (condition) { body }`
 */
export type GuardedStatement =
  | ts.ForStatement
  | ts.ForOfStatement
  | ts.ForInStatement
  | ts.IfStatement;

/**
 * Represents a parsed bound check like `i < arr.length` or `arr.length > 0`.
 */
export type BoundCheck = {
  index: string;
  arrayVar: string;
};

/**
 * Parsed simple element access like `arr[i]` or `arr[0]`.
 * Same structure as BoundCheck for easy comparison.
 */
export type ElementAccess = {
  arrayVar: string;
  index: string;
};

// =============================================================================
// Simple expression text helpers
// =============================================================================

/**
 * Get text representation of a "simple" expression.
 * Handles identifiers, `this`, and property access chains.
 * Returns undefined for complex expressions (calls, element access, etc.).
 */
export function getSimpleExpressionText(
  tsMod: typeof import("typescript"),
  expr: ts.Expression,
): string | undefined {
  if (tsMod.isIdentifier(expr)) {
    return expr.text;
  }
  if (expr.kind === tsMod.SyntaxKind.ThisKeyword) {
    return "this";
  }
  if (tsMod.isPropertyAccessExpression(expr)) {
    const base = getSimpleExpressionText(tsMod, expr.expression);
    if (base === undefined) return undefined;
    return base + "." + expr.name.text;
  }
  return undefined;
}

// =============================================================================
// Bound check parsing
// =============================================================================

/**
 * Try to parse the index part of a bound check (identifier or numeric literal).
 */
function parseBoundCheckIndex(
  tsMod: typeof import("typescript"),
  expr: ts.Expression,
): string | undefined {
  if (tsMod.isIdentifier(expr)) {
    return expr.text;
  }
  if (tsMod.isNumericLiteral(expr)) {
    return expr.text;
  }
  return undefined;
}

/**
 * Try to parse arr.length from an expression.
 * Returns the array expression text if successful.
 * Supports both simple identifiers (arr.length) and property chains (obj.arr.length).
 */
function parseArrayLength(
  tsMod: typeof import("typescript"),
  expr: ts.Expression,
): string | undefined {
  if (!tsMod.isPropertyAccessExpression(expr)) return undefined;
  if (expr.name.text !== "length") return undefined;
  return getSimpleExpressionText(tsMod, expr.expression);
}

/**
 * Try to parse a condition as a bound check.
 * Recognizes two patterns:
 * - `index < arr.length` (index on left)
 * - `arr.length > index` (index on right, symmetric)
 *
 * Only strict inequality (<, >) is allowed, not <= or >=.
 * Returns undefined if the condition doesn't match.
 */
export function parseBoundCheck(
  tsMod: typeof import("typescript"),
  condition: ts.Expression,
): BoundCheck | undefined {
  if (!tsMod.isBinaryExpression(condition)) return undefined;

  const op = condition.operatorToken.kind;

  // Pattern 1: index < arr.length
  if (op === tsMod.SyntaxKind.LessThanToken) {
    const index = parseBoundCheckIndex(tsMod, condition.left);
    const arrayVar = parseArrayLength(tsMod, condition.right);
    if (index && arrayVar) {
      return { index, arrayVar };
    }
  }

  // Pattern 2: arr.length > index (symmetric)
  if (op === tsMod.SyntaxKind.GreaterThanToken) {
    const arrayVar = parseArrayLength(tsMod, condition.left);
    const index = parseBoundCheckIndex(tsMod, condition.right);
    if (index && arrayVar) {
      return { index, arrayVar };
    }
  }

  return undefined;
}

// =============================================================================
// Early-exit guard analysis
// =============================================================================

/**
 * Check if a statement is an early-exit statement.
 * Supported: return, throw, continue (unlabeled), break (unlabeled)
 */
function isEarlyExitStatement(
  tsMod: typeof import("typescript"),
  stmt: ts.Statement,
): boolean {
  if (tsMod.isReturnStatement(stmt)) return true;
  if (tsMod.isThrowStatement(stmt)) return true;
  if (tsMod.isContinueStatement(stmt) && !stmt.label) return true;
  if (tsMod.isBreakStatement(stmt) && !stmt.label) return true;
  return false;
}

/**
 * Get the single early-exit statement from an if-statement's then-branch.
 * Returns the exit statement if the then-branch is either:
 * - A single exit statement: `if (...) return;`
 * - A block with exactly one exit statement: `if (...) { return; }`
 */
function getSingleEarlyExitStatement(
  tsMod: typeof import("typescript"),
  thenBranch: ts.Statement,
): ts.Statement | undefined {
  // Direct statement: `if (...) return;`
  if (isEarlyExitStatement(tsMod, thenBranch)) {
    return thenBranch;
  }
  // Block with single statement: `if (...) { return; }`
  if (tsMod.isBlock(thenBranch) && thenBranch.statements.length === 1) {
    const stmt = thenBranch.statements[0];
    if (isEarlyExitStatement(tsMod, stmt)) {
      return stmt;
    }
  }
  return undefined;
}

/**
 * Parse an early-exit guard as a BoundCheck.
 *
 * Patterns (no else, single early-exit in the body):
 * - `if (arr.length === 0) { exit }` (or `==`, symmetric `0 === arr.length`)
 * - `if (arr.length <= n) { exit }` (or `n >= arr.length`)
 *
 * After such a guard, we can derive a strict lower-bound check `n < arr.length`,
 * which matches the existing BoundCheck representation.
 *
 * Returns BoundCheck { arrayVar, index: n } or undefined.
 */
export function parseEarlyExitBoundCheck(
  tsMod: typeof import("typescript"),
  ifStmt: ts.IfStatement,
): BoundCheck | undefined {
  // 1. Must have no else clause
  if (ifStmt.elseStatement) return undefined;

  // 2. Then-branch must be a single early-exit statement
  if (!getSingleEarlyExitStatement(tsMod, ifStmt.thenStatement)) return undefined;

  // 3. Parse condition
  const condition = ifStmt.expression;
  if (!tsMod.isBinaryExpression(condition)) return undefined;

  const op = condition.operatorToken.kind;

  // Pattern: arr.length === 0 or arr.length == 0
  if (
    op === tsMod.SyntaxKind.EqualsEqualsEqualsToken ||
    op === tsMod.SyntaxKind.EqualsEqualsToken
  ) {
    // Try: arr.length === 0
    const arrayVar = parseArrayLength(tsMod, condition.left);
    if (arrayVar && tsMod.isNumericLiteral(condition.right) && condition.right.text === "0") {
      return { arrayVar, index: "0" };
    }
    // Try symmetric: 0 === arr.length
    const arrayVarSym = parseArrayLength(tsMod, condition.right);
    if (arrayVarSym && tsMod.isNumericLiteral(condition.left) && condition.left.text === "0") {
      return { arrayVar: arrayVarSym, index: "0" };
    }
  }

  // Pattern: arr.length <= n
  if (op === tsMod.SyntaxKind.LessThanEqualsToken) {
    const arrayVar = parseArrayLength(tsMod, condition.left);
    const index = parseBoundCheckIndex(tsMod, condition.right);
    if (arrayVar && index) {
      return { arrayVar, index };
    }
  }

  // Pattern: n >= arr.length (symmetric)
  if (op === tsMod.SyntaxKind.GreaterThanEqualsToken) {
    const arrayVar = parseArrayLength(tsMod, condition.right);
    const index = parseBoundCheckIndex(tsMod, condition.left);
    if (arrayVar && index) {
      return { arrayVar, index };
    }
  }

  return undefined;
}

/**
 * Find an immediately-preceding early-exit guard that establishes a bound check.
 * The guard must be in the same block/source file and directly precede the statement.
 */
export function findPrecedingEarlyExitBoundCheck(
  tsMod: typeof import("typescript"),
  stmt: ts.Statement,
): BoundCheck | undefined {
  const parent = stmt.parent;

  // Must be in a block or source file
  if (!tsMod.isBlock(parent) && !tsMod.isSourceFile(parent)) return undefined;

  const statements = parent.statements;

  // Find the statement's index using explicit iteration
  let index = -1;
  for (let i = 0; i < statements.length; i++) {
    if (statements[i] === stmt) {
      index = i;
      break;
    }
  }

  // Must have a preceding statement
  if (index <= 0) return undefined;

  const precedingStmt = statements[index - 1];

  // Preceding statement must be an if-statement
  if (!tsMod.isIfStatement(precedingStmt)) return undefined;

  return parseEarlyExitBoundCheck(tsMod, precedingStmt);
}

// =============================================================================
// Element access parsing
// =============================================================================

/**
 * Try to parse an element access expression (arr[index] or obj.arr[index]).
 * Returns undefined if not a simple pattern.
 */
export function tryParseElementAccess(
  tsMod: typeof import("typescript"),
  expr: ts.Expression,
): ElementAccess | undefined {
  if (!tsMod.isElementAccessExpression(expr)) return undefined;

  const arrayExpr = expr.expression;
  const indexExpr = expr.argumentExpression;

  // Array must be a simple expression (identifier or property chain)
  const arrayVar = getSimpleExpressionText(tsMod, arrayExpr);
  if (arrayVar === undefined) return undefined;

  // Index must be identifier or literal
  if (!indexExpr) return undefined;
  let index: string;
  if (tsMod.isIdentifier(indexExpr)) {
    index = indexExpr.text;
  } else if (tsMod.isNumericLiteral(indexExpr) || tsMod.isStringLiteral(indexExpr)) {
    index = indexExpr.text;
  } else {
    return undefined;
  }

  return { arrayVar, index };
}

/**
 * Check if a bound check matches an element access.
 */
export function boundCheckMatchesElementAccess(
  boundCheck: BoundCheck,
  elementAccess: ElementAccess,
): boolean {
  return boundCheck.arrayVar === elementAccess.arrayVar && boundCheck.index === elementAccess.index;
}

// =============================================================================
// Safe evaluation position checkers
// =============================================================================

/**
 * A safe evaluation checker determines if a node is in a position where
 * no side effects happen before evaluating it within a statement.
 * Returns the containing statement if the position is safe.
 */
type SafeEvaluationChecker = (
  tsMod: typeof import("typescript"),
  node: ts.Node,
) => ts.Statement | undefined;

/**
 * Check: node is the RHS of an assignment or variable declaration.
 * Pattern: `const x = expr!` or `x = expr!`
 */
function checkAssignmentPosition(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Statement | undefined {
  // Check variable declaration: const x = expr!
  const parent = node.parent;
  if (parent && tsMod.isVariableDeclaration(parent) && parent.initializer === node) {
    const declList = parent.parent;
    if (declList && tsMod.isVariableDeclarationList(declList)) {
      const varStmt = declList.parent;
      if (varStmt && tsMod.isVariableStatement(varStmt)) {
        return varStmt;
      }
    }
  }

  // Check assignment expression: x = expr!
  const assignment = isRhsOfBinaryOp(tsMod, node, tsMod.SyntaxKind.EqualsToken);
  if (assignment) {
    return getContainingStatement(tsMod, assignment);
  }

  return undefined;
}

/**
 * Check: node is the first argument of a call expression.
 * Pattern: `result.push(expr!)`
 */
function checkFirstCallArgPosition(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Statement | undefined {
  const parent = node.parent;
  if (!parent || !tsMod.isCallExpression(parent)) return undefined;

  const args = parent.arguments;
  if (args.length === 0 || args[0] !== node) return undefined;

  const callParent = parent.parent;
  if (callParent && tsMod.isExpressionStatement(callParent)) {
    return callParent;
  }

  return undefined;
}

/**
 * Check: node is the expression of a return statement.
 * Pattern: `return expr!`
 */
function checkReturnPosition(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Statement | undefined {
  const parent = node.parent;
  if (!parent || !tsMod.isReturnStatement(parent)) return undefined;
  if (parent.expression !== node) return undefined;
  return parent;
}

/**
 * Registry of safe evaluation checkers.
 * Each checker returns the containing statement if the node is in a safe
 * evaluation position (no side effects before evaluation).
 */
const SAFE_EVALUATION_CHECKERS: SafeEvaluationChecker[] = [
  checkAssignmentPosition,
  checkFirstCallArgPosition,
  checkReturnPosition,
];

/**
 * Get the containing statement if node is in a safe evaluation position.
 * A safe position is one where no side effects happen before evaluating the node.
 */
export function getStatementForSafeEvaluation(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Statement | undefined {
  for (const checker of SAFE_EVALUATION_CHECKERS) {
    const stmt = checker(tsMod, node);
    if (stmt) return stmt;
  }
  return undefined;
}

// =============================================================================
// Guarded statement analysis
// =============================================================================

/**
 * Check if a block is the body of a guarded statement (for-loop or if).
 */
function isGuardedStatementBody(
  tsMod: typeof import("typescript"),
  block: ts.Block,
): GuardedStatement | undefined {
  return isForLoopBody(tsMod, block) ?? isIfStatementBody(tsMod, block);
}

/**
 * Get the guarded statement if a statement is the first in a guarded body.
 * Returns the for-loop or if-statement that guards the body.
 */
function getGuardForFirstStatement(
  tsMod: typeof import("typescript"),
  stmt: ts.Statement,
): GuardedStatement | undefined {
  const block = isFirstStatementInBlock(tsMod, stmt);
  if (!block) return undefined;
  return isGuardedStatementBody(tsMod, block);
}

/**
 * Get the containing guarded statement if node is in a "safe" position.
 * Combines two checks:
 * 1. Node is in a safe evaluation position (no side effects before evaluation)
 * 2. The containing statement is the first in a guarded body (for-loop or if-statement)
 */
export function getGuardedStatementForSafePosition(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): GuardedStatement | undefined {
  const stmt = getStatementForSafeEvaluation(tsMod, node);
  if (!stmt) return undefined;
  return getGuardForFirstStatement(tsMod, stmt);
}

/**
 * Extract the guard condition from a guarded statement.
 * - ForStatement: returns the condition expression
 * - IfStatement: returns the condition expression
 * - ForOfStatement/ForInStatement: returns undefined (no bound check)
 */
export function getGuardCondition(
  tsMod: typeof import("typescript"),
  stmt: GuardedStatement,
): ts.Expression | undefined {
  if (tsMod.isForStatement(stmt)) {
    return stmt.condition;
  }
  if (tsMod.isIfStatement(stmt)) {
    return stmt.expression;
  }
  // ForOfStatement and ForInStatement don't have a comparable condition
  return undefined;
}

// =============================================================================
// Conditional expression helpers
// =============================================================================

/**
 * Get the condition if node is the "whenTrue" branch of a conditional expression.
 * Pattern: `condition ? node : other`
 */
export function getConditionalExpressionCondition(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Expression | undefined {
  const parent = node.parent;
  if (!parent || !tsMod.isConditionalExpression(parent)) return undefined;
  if (parent.whenTrue !== node) return undefined;
  return parent.condition;
}

// =============================================================================
// Side-effect-free wrapper analysis
// =============================================================================

/**
 * A side-effect-free wrapper checker determines if a node's parent is a
 * wrapper that doesn't introduce side effects before evaluating the node.
 * Returns the parent expression if it's a safe wrapper, undefined otherwise.
 *
 * This allows patterns like `arr[i]!.foo.bar` where property accesses wrap
 * the non-null assertion but don't introduce any computation before
 * the array access is evaluated.
 */
type SideEffectFreeWrapperChecker = (
  tsMod: typeof import("typescript"),
  node: ts.Node,
) => ts.Expression | undefined;

/**
 * Check: parent is a property access where node is the expression being accessed.
 * Pattern: `node.foo` - property access doesn't introduce side effects.
 */
function checkPropertyAccessWrapper(
  tsMod: typeof import("typescript"),
  node: ts.Node,
): ts.Expression | undefined {
  const parent = node.parent;
  if (!parent || !tsMod.isPropertyAccessExpression(parent)) return undefined;
  if (parent.expression !== node) return undefined;
  return parent;
}

/**
 * Registry of side-effect-free wrapper checkers.
 * Add new patterns here to extend what's considered a safe wrapper.
 */
const SIDE_EFFECT_FREE_WRAPPER_CHECKERS: SideEffectFreeWrapperChecker[] = [
  checkPropertyAccessWrapper,
];

/**
 * Walk up through side-effect-free wrappers to find the outermost expression.
 * Property accesses like `.foo.bar.baz` don't introduce side effects before
 * evaluating the inner expression, so `arr[i]!.foo.bar` is safe if the
 * outermost expression `arr[i]!.foo.bar` is in a safe position.
 */
export function getOutermostSideEffectFreeExpression(
  tsMod: typeof import("typescript"),
  node: ts.Expression,
): ts.Expression {
  let current: ts.Expression = node;
  while (true) {
    let wrapped = false;
    for (const checker of SIDE_EFFECT_FREE_WRAPPER_CHECKERS) {
      const wrapper = checker(tsMod, current);
      if (wrapper) {
        current = wrapper;
        wrapped = true;
        break;
      }
    }
    if (!wrapped) break;
  }
  return current;
}
