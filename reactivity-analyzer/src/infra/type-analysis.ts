/**
 * Type analysis utilities using the TypeScript type checker.
 */

import type ts from "typescript";

/**
 * Check if a type assertion is necessary.
 * Returns true if the expression type is NOT assignable to the target type.
 *
 * Uses the TypeScript type checker's `isTypeAssignableTo` API.
 */
export function isTypeAssertionNecessary(
  typeChecker: ts.TypeChecker,
  asExpr: ts.AsExpression,
): boolean {
  const exprType = typeChecker.getTypeAtLocation(asExpr.expression);
  const targetType = typeChecker.getTypeFromTypeNode(asExpr.type);

  // If expression type is assignable to target, assertion is unnecessary.
  return !typeChecker.isTypeAssignableTo(exprType, targetType);
}

/**
 * Check if the expression in a type assertion has type `Json`.
 */
export function isExpressionTypeJson(
  typeChecker: ts.TypeChecker,
  asExpr: ts.AsExpression,
): boolean {
  const exprType = typeChecker.getTypeAtLocation(asExpr.expression);
  const symbol = exprType.aliasSymbol ?? exprType.getSymbol();
  return symbol?.getName() === "Json";
}

/**
 * Check if an assertion is part of a double-cast bridge pattern `x as unknown as T`.
 *
 * Returns true for:
 * - The inner `x as unknown` when parent is another AsExpression
 * - The outer `... as T` when the expression is `x as unknown`
 */
export function isDoubleCastBridge(
  tsMod: typeof import("typescript"),
  typeChecker: ts.TypeChecker,
  asExpr: ts.AsExpression,
): boolean {
  const targetType = typeChecker.getTypeFromTypeNode(asExpr.type);
  const isTargetUnknown = (targetType.flags & tsMod.TypeFlags.Unknown) !== 0;

  // Inner part: `x as unknown` where parent is also an AsExpression
  if (isTargetUnknown && tsMod.isAsExpression(asExpr.parent)) {
    return true;
  }

  // Outer part: `(x as unknown) as T` where expression is an `as unknown` cast
  if (tsMod.isAsExpression(asExpr.expression)) {
    const innerTarget = typeChecker.getTypeFromTypeNode(asExpr.expression.type);
    if ((innerTarget.flags & tsMod.TypeFlags.Unknown) !== 0) {
      return true;
    }
  }

  return false;
}
