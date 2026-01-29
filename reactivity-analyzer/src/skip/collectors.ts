/**
 * Skip-specific collectors for the reactivity analyzer.
 *
 * Extracts Skip service/mapper information from TypeScript AST.
 */

import ts from "typescript";
import {
  createNodeIterator,
  getImplementsNames,
  getLineCol,
  type AnalyzerContext,
} from "../infra/ast-inspection.js";
import type {
  FileAnalysis,
  ServiceClassMember,
  ServiceClassMemberKind,
} from "./report.js";
import type { Violation } from "../infra/checker.js";
import { DEFAULT_ENABLED_CHECKERS, setupAstCheckers, type CheckerName } from "./checkers/index.js";

type ProgramContext = AnalyzerContext<FileAnalysis> & {
  enabledCheckers: Set<CheckerName>;
};

export type AnalysisResult = {
  analysis: FileAnalysis;
  violations: Violation[];
};

export type AnalyzeOptions = {
  enabledCheckers?: Set<CheckerName>;
};

/**
 * A mapper class is a class that implements an interface whose name ends in "Mapper".
 */
function isMapperClass(
  tsMod: typeof import("typescript"),
  node: ts.ClassDeclaration,
): boolean {
  const implementsNames = getImplementsNames(tsMod, node.heritageClauses);
  return implementsNames.some((name) => name.endsWith("Mapper"));
}

/**
 * A service class is a class that implements an interface named exactly "SkipService".
 */
function isServiceClass(
  tsMod: typeof import("typescript"),
  node: ts.ClassDeclaration,
): boolean {
  const implementsNames = getImplementsNames(tsMod, node.heritageClauses);
  return implementsNames.some((name) => name === "SkipService");
}

function collectMapperClasses(node: ts.ClassDeclaration, ctx: ProgramContext): void {
  const { ts: tsMod, sourceFile, report } = ctx;
  if (!node.name) return;
  if (!isMapperClass(tsMod, node)) return;

  const implementsNames = getImplementsNames(tsMod, node.heritageClauses);
  const implementsType = implementsNames.find((name) => name.endsWith("Mapper"));
  if (!implementsType) return;
  report.mapperClasses.push({
    name: node.name.text,
    implementsType,
    pos: getLineCol(sourceFile, node.getStart(sourceFile)),
    file: sourceFile.fileName,
  });
}

function collectServiceClasses(node: ts.ClassDeclaration, ctx: ProgramContext): void {
  const { ts: tsMod, sourceFile, report } = ctx;
  if (!node.name) return;
  if (!isServiceClass(tsMod, node)) return;

  const members: ServiceClassMember[] = [];
  for (const member of node.members) {
    let name: string | null = null;
    if (member.name && tsMod.isIdentifier(member.name)) {
      name = member.name.text;
    }

    let kind: ServiceClassMemberKind = "unknown";
    if (tsMod.isConstructorDeclaration(member)) {
      kind = "constructor";
    } else if (tsMod.isPropertyDeclaration(member)) {
      kind = "property";
    } else if (tsMod.isMethodDeclaration(member)) {
      kind = "method";
    } else if (tsMod.isGetAccessorDeclaration(member) || tsMod.isSetAccessorDeclaration(member)) {
      kind = "accessor";
    }

    members.push({
      name,
      kind,
      pos: getLineCol(sourceFile, member.getStart(sourceFile)),
    });
  }

  report.serviceClasses.push({
    name: node.name.text,
    implementsType: "SkipService",
    pos: getLineCol(sourceFile, node.getStart(sourceFile)),
    file: sourceFile.fileName,
    members,
  });
}

function collectMapCalls(node: ts.CallExpression, ctx: ProgramContext): void {
  const { ts: tsMod, typeChecker, sourceFile, report } = ctx;
  const expr = node.expression;
  if (!tsMod.isPropertyAccessExpression(expr)) return;
  if (!tsMod.isIdentifier(expr.name) || expr.name.text !== "map") return;

  const prop = expr;
  const receiver = prop.expression;
  const argsArr = node.arguments;
  const mapperArg = argsArr.length > 0 ? argsArr[0] : null;

  const mapperResolved = mapperArg
    ? (() => {
        const sym = typeChecker.getSymbolAtLocation(mapperArg);
        return sym ? sym.getName() : null;
      })()
    : null;

  report.mapCalls.push({
    pos: getLineCol(sourceFile, node.getStart(sourceFile)),
    file: sourceFile.fileName,
    receiverText: receiver.getText(sourceFile),
    mapperText: mapperArg ? mapperArg.getText(sourceFile) : "<missing>",
    mapperResolved,
    paramsCount: Math.max(0, argsArr.length - 1),
  });
}

export function analyzeProgram(
  tsMod: typeof import("typescript"),
  args: { program: ts.Program; sourceFile: ts.SourceFile },
  options: AnalyzeOptions = {},
): AnalysisResult {
  const { enabledCheckers = new Set(DEFAULT_ENABLED_CHECKERS) } = options;

  const analysis: FileAnalysis = {
    mapperClasses: [],
    serviceClasses: [],
    mapCalls: [],
    sourceFile: args.sourceFile.fileName,
  };
  const ctx: ProgramContext = {
    ts: tsMod,
    typeChecker: args.program.getTypeChecker(),
    sourceFile: args.sourceFile,
    report: analysis,
    violations: [], // unused, kept for AnalyzerContext compatibility
    enabledCheckers,
  };

  const visitor = createNodeIterator(ctx);
  visitor.on(tsMod.isClassDeclaration, (node) => collectMapperClasses(node, ctx));
  visitor.on(tsMod.isClassDeclaration, (node) => collectServiceClasses(node, ctx));
  visitor.on(tsMod.isCallExpression, (node) => collectMapCalls(node, ctx));
  setupAstCheckers(visitor, ctx);
  const violations = visitor.run();

  return { analysis, violations };
}
