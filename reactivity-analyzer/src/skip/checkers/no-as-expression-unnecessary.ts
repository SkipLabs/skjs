/**
 * Checker: flag unnecessary type assertions (`as` expressions).
 *
 * An assertion is unnecessary when the expression type is already assignable
 * to the target type. Skips `as unknown` (pass-through for double-cast patterns).
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import { isDoubleCastBridge, isTypeAssertionNecessary } from "../../infra/type-analysis.js";
import type { Checker } from "./types.js";

const NAME = "no-as-expression-unnecessary";

export const noAsExpressionUnnecessaryChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, sourceFile, typeChecker } = ctx;

    visitor.on(tsMod.isAsExpression, (node: ts.AsExpression) => {
      // Skip double-cast bridge patterns: `x as unknown as T`
      if (isDoubleCastBridge(tsMod, typeChecker, node)) {
        return [];
      }
      if (isTypeAssertionNecessary(typeChecker, node)) {
        return [];
      }

      const text = node.getText(sourceFile);
      const pos = getLineCol(sourceFile, node.getStart(sourceFile));
      return [
        {
          checker: NAME,
          message: "Unnecessary type assertion: " + text,
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
