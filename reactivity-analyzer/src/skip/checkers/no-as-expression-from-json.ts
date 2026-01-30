/**
 * Checker: flag type assertions from `Json` type.
 *
 * Flags patterns like `params as SomeResourceParams` where the expression
 * has type `Json`. Use `no-as-expression-necessary` for other necessary casts.
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import { isExpressionTypeJson, isTypeAssertionNecessary } from "../../infra/type-analysis.js";
import type { Checker } from "./types.js";

const NAME = "no-as-expression-from-json";

export const noAsExpressionFromJsonChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, sourceFile, typeChecker } = ctx;

    visitor.on(tsMod.isAsExpression, (node: ts.AsExpression) => {
      // Only flag necessary assertions from Json type
      if (!isTypeAssertionNecessary(typeChecker, node)) {
        return [];
      }
      if (!isExpressionTypeJson(typeChecker, node)) {
        return [];
      }

      const text = node.getText(sourceFile);
      const pos = getLineCol(sourceFile, node.getStart(sourceFile));
      return [
        {
          checker: NAME,
          message: "Type assertion from Json: " + text,
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
