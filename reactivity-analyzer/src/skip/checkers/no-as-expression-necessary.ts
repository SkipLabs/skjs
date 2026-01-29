/**
 * Checker: flag necessary type assertions (`as` expressions).
 *
 * An assertion is necessary when the expression type is NOT assignable
 * to the target type. Use `no-as-expression-unnecessary` for the inverse.
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import { isTypeAssertionNecessary } from "../../infra/type-analysis.js";
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
