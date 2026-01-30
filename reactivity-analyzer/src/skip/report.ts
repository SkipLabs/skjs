/**
 * Skip-specific report types for the reactivity analyzer.
 */

// Import and re-export LineCol from infra for convenience
import type { LineCol } from "../infra/ast-inspection.js";
export type { LineCol };

export type MapperClassDecl = {
  name: string;
  implementsType: string;
  pos: LineCol;
  file: string;
};

export type ServiceClassDecl = {
  name: string;
  implementsType: "SkipService";
  pos: LineCol;
  file: string;
  members: ServiceClassMember[];
};

export type ServiceClassMemberKind =
  | "constructor"
  | "property"
  | "method"
  | "accessor"
  | "unknown";

export type ServiceClassMember = {
  name: string | null;
  kind: ServiceClassMemberKind;
  pos: LineCol;
};

export type MapCallsite = {
  pos: LineCol;
  file: string;
  receiverText: string;
  mapperText: string;
  mapperResolved: string | null;
  paramsCount: number;
};

export type FileAnalysis = {
  mapperClasses: MapperClassDecl[];
  serviceClasses: ServiceClassDecl[];
  mapCalls: MapCallsite[];
  sourceFile: string;
};

export function mergeFileAnalyses(analyses: FileAnalysis[]): FileAnalysis {
  const merged: FileAnalysis = {
    mapperClasses: [],
    serviceClasses: [],
    mapCalls: [],
    sourceFile: analyses.length > 0 ? analyses[0]!.sourceFile : "",
  };

  for (const analysis of analyses) {
    merged.mapperClasses.push(...analysis.mapperClasses);
    merged.serviceClasses.push(...analysis.serviceClasses);
    merged.mapCalls.push(...analysis.mapCalls);
  }

  return merged;
}
