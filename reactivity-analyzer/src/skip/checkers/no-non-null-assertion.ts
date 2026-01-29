/**
 * Checker: forbid postfix non-null assertions (`!`) except for safe patterns.
 *
 * This checker flags uses of the postfix ! operator, with exceptions for
 * safe patterns like array access inside bounded for-loops or if-statements.
 *
 * Safe patterns allowed:
 * - `arr[i]!` where i < arr.length is checked in a for-loop or if-statement
 * - `cond ? arr[i]! : other` where cond includes a bound check
 * - Side-effect-free wrappers like `arr[i]!.foo.bar`
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import {
  boundCheckMatchesElementAccess,
  getConditionalExpressionCondition,
  getGuardCondition,
  getGuardedStatementForSafePosition,
  getOutermostSideEffectFreeExpression,
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
      // Allow pattern: safe position with a bound check on a simple array access (arr[i]!)
      // Supported guard contexts:
      // - Guarded statements: for-loops and if-statements (first statement in body)
      // - Conditional expressions: `cond ? arr[i]! : other` (whenTrue branch)
      // Also allows side-effect-free wrappers like arr[i]!.foo.bar
      const outerExpr = getOutermostSideEffectFreeExpression(tsMod, node);
      const elementAccess = tryParseElementAccess(tsMod, node.expression);

      if (elementAccess) {
        // Try guarded statement (for/if body)
        const guardedStmt = getGuardedStatementForSafePosition(tsMod, outerExpr);
        const condition = guardedStmt
          ? getGuardCondition(tsMod, guardedStmt)
          : getConditionalExpressionCondition(tsMod, outerExpr);

        const boundCheck = parseBoundCheck(tsMod, condition);
        if (boundCheck && boundCheckMatchesElementAccess(boundCheck, elementAccess)) {
          return [];
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
