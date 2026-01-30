/**
 * Checker: forbid postfix non-null assertions (`!`) except for guarded array access.
 *
 * Allows `arr[i]!` when a bound check (`i < arr.length` or equivalent) is established
 * by a guard. See inline comments for supported patterns.
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import {
  boundCheckMatchesElementAccess,
  findPrecedingEarlyExitBoundCheck,
  getConditionalExpressionCondition,
  getGuardCondition,
  getGuardedStatementForSafePosition,
  getOutermostSideEffectFreeExpression,
  getStatementForSafeEvaluation,
  parseBoundCheck,
  tryParseElementAccess,
} from "../../infra/guard-analysis.js";
import type { Checker } from "./types.js";

const NAME = "no-non-null-assertion";

export const noNonNullAssertionChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, sourceFile } = ctx;

    visitor.on(tsMod.isNonNullExpression, (node: ts.NonNullExpression) => {
      // Allow side-effect-free wrappers like arr[i]!.foo.bar
      const outerExpr = getOutermostSideEffectFreeExpression(tsMod, node);
      const elementAccess = tryParseElementAccess(tsMod, node.expression);

      if (elementAccess) {
        // Pattern 1: Guarded body - first statement in for-loop or if with bound check
        // Example: for (let i = 0; i < arr.length; i++) { const x = arr[i]!; }
        const guardedStmt = getGuardedStatementForSafePosition(tsMod, outerExpr);

        // Pattern 2: Ternary - whenTrue branch with bound check condition
        // Example: const x = i < arr.length ? arr[i]! : fallback;
        const condition = guardedStmt
          ? getGuardCondition(tsMod, guardedStmt)
          : getConditionalExpressionCondition(tsMod, outerExpr);

        // Check if patterns 1 or 2 establish a matching bound check (i < arr.length)
        if (condition) {
          const boundCheck = parseBoundCheck(tsMod, condition);
          if (boundCheck && boundCheckMatchesElementAccess(boundCheck, elementAccess)) {
            return [];
          }
        }

        // Pattern 3: Early-exit guard - immediately preceding if with exit
        // Example: if (arr.length === 0) { return; } const x = arr[0]!;
        // Supports: === 0, <= n; exits: return, throw, continue, break (unlabeled)
        const useStmt = getStatementForSafeEvaluation(tsMod, outerExpr);
        if (useStmt) {
          const earlyExitBoundCheck = findPrecedingEarlyExitBoundCheck(tsMod, useStmt);
          if (earlyExitBoundCheck && boundCheckMatchesElementAccess(earlyExitBoundCheck, elementAccess)) {
            return [];
          }
        }
      }

      const text = node.getText(sourceFile);
      const pos = getLineCol(sourceFile, node.getStart(sourceFile));
      return [
        {
          checker: NAME,
          message: "Non-null assertion: `" + text + "`",
          file: sourceFile.fileName,
          pos: withEndCol(pos, text),
          details: {
            expression: node.expression.getText(sourceFile),
          },
        },
      ];
    });
  },
};
