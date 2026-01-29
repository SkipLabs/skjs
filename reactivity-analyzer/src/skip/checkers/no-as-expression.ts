/**
 * Checker: forbid type assertions (`as` expressions).
 */

import type ts from "typescript";
import { getLineCol, withEndCol } from "../../infra/ast-inspection.js";
import type { Checker } from "./types.js";

const NAME = "no-as-expression";

export const noAsExpressionChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, sourceFile } = ctx;
    visitor.on(tsMod.isAsExpression, (node: ts.AsExpression) => {
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
