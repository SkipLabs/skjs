/**
 * Checker: Values<T> parameters in Mapper.mapEntry can only be used via `.toArray()`.
 */

import type ts from "typescript";
import {
  collectIdentifierUses,
  findMethodBody,
  getImplementsNames,
  getLineCol,
  getTypeReferenceArgs,
  isIdentifierPropertyCall,
  withEndCol,
} from "../../infra/ast-inspection.js";
import type { Checker } from "./types.js";

const NAME = "mapentry-values-toarray";

function isMapperClass(
  tsMod: typeof import("typescript"),
  node: ts.ClassDeclaration,
): boolean {
  const implementsNames = getImplementsNames(tsMod, node.heritageClauses);
  return implementsNames.some((name) => name.endsWith("Mapper"));
}

export const mapEntryValuesToArrayChecker: Checker = {
  name: NAME,
  onAstTraversal: (visitor, ctx) => {
    const { ts: tsMod, typeChecker, sourceFile } = ctx;

    visitor.on(tsMod.isClassDeclaration, (node: ts.ClassDeclaration) => {
      if (!node.name) return [];
      if (!isMapperClass(tsMod, node)) return [];

      const body = findMethodBody(tsMod, node, "mapEntry");
      if (!body) return [];

      const mapEntry = node.members.find(
        (m) =>
          tsMod.isMethodDeclaration(m) &&
          m.name &&
          tsMod.isIdentifier(m.name) &&
          m.name.text === "mapEntry",
      );
      if (!mapEntry || !tsMod.isMethodDeclaration(mapEntry)) return [];

      let valuesParamName: string | null = null;
      for (const param of mapEntry.parameters) {
        const paramType = typeChecker.getTypeAtLocation(param);
        const args = getTypeReferenceArgs(tsMod, typeChecker, paramType, "Values");
        if (args && args.length === 1 && tsMod.isIdentifier(param.name)) {
          valuesParamName = param.name.text;
          break;
        }
      }

      if (!valuesParamName) return [];

      const violations: import("../../infra/checker.js").Violation[] = [];
      const uses = collectIdentifierUses(tsMod, sourceFile, body, valuesParamName);
      for (const use of uses) {
        const isAllowed = isIdentifierPropertyCall(tsMod, use.id, "toArray");
        if (!isAllowed) {
          violations.push({
            checker: NAME,
            message:
              "mapEntry uses '" +
              valuesParamName +
              "' in a way other than " +
              valuesParamName +
              ".toArray(): " +
              use.text,
            file: sourceFile.fileName,
            pos: withEndCol(use.pos, use.text),
            details: {
              className: node.name.text,
              valuesParamName,
              at: getLineCol(sourceFile, use.id.getStart(sourceFile)),
            },
          });
        }
      }
      return violations;
    });
  },
};
