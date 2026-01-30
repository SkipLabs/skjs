/**
 * Checker: flag necessary type assertions (`as` expressions).
 *
 * An assertion is necessary when the expression type is NOT assignable
 * to the target type. Excludes casts from `Json` and double-cast patterns with `unknown`.
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import { isDoubleCastBridge, isExpressionTypeJson, isTypeAssertionNecessary } from "../../infra/type-analysis.js";
import type { Checker } from "./types.js";

const NAME = "no-as-expression-necessary";

export const noAsExpressionNecessaryChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, sourceFile, typeChecker } = ctx;

    visitor.on(tsMod.isAsExpression, (node: ts.AsExpression) => {
      if (!isTypeAssertionNecessary(typeChecker, node)) {
        return [];
      }
      // Json casts are handled by no-as-expression-from-json
      if (isExpressionTypeJson(typeChecker, node)) {
        return [];
      }
      // Skip double-cast bridge patterns: `x as unknown as T`
      if (isDoubleCastBridge(tsMod, typeChecker, node)) {
        return [];
      }

      const text = node.getText(sourceFile);
      const pos = getLineCol(sourceFile, node.getStart(sourceFile));
      return [
        {
          checker: NAME,
          message: "Type assertion (as) used: " + text,
          file: sourceFile.fileName,
          pos: withEndCol(pos, text),
          details: {
            expression: node.expression.getText(sourceFile),
            targetType: node.type.getText(sourceFile),
          },
        },
      ];
    });
  },
};
