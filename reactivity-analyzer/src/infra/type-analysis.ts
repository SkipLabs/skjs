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
