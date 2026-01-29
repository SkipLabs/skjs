/**
 * Checker registry for the reactivity analyzer.
 *
 * Each checker lives in `checkers/` and can participate in one or more phases:
 * - `onAstTraversal`: during AST traversal, handlers return violations
 * - `onMergedReport`: after analysis on the merged report, returns violations
 */

import type { NodeIterator } from "../../infra/ast-inspection.js";
import type { Violation } from "../../infra/checker.js";
import type { FileAnalysis } from "../report.js";
import { mapEntryValuesToArrayChecker } from "./mapentry-values-toarray.js";
import { noAsExpressionFromJsonChecker } from "./no-as-expression-from-json.js";
import { noAsExpressionNecessaryChecker } from "./no-as-expression-necessary.js";
import { noAsExpressionUnnecessaryChecker } from "./no-as-expression-unnecessary.js";
import { noNonNullAssertionChecker } from "./no-non-null-assertion.js";
import { serviceCountChecker } from "./service-count.js";
import { serviceMembersChecker } from "./service-members.js";
import { CHECKER_NAMES, type Checker, type CheckerContext, type CheckerName } from "./types.js";

export { CHECKER_NAMES };
export type { Checker, CheckerContext, CheckerName };

export const ALL_CHECKERS: Checker[] = [
  noAsExpressionFromJsonChecker,
  noAsExpressionNecessaryChecker,
  noAsExpressionUnnecessaryChecker,
  noNonNullAssertionChecker,
  mapEntryValuesToArrayChecker,
  serviceCountChecker,
  serviceMembersChecker,
];

export const ALL_CHECKER_NAMES: readonly CheckerName[] = CHECKER_NAMES;

export const DEFAULT_ENABLED_CHECKERS: Set<CheckerName> = new Set(CHECKER_NAMES);

export function isKnownCheckerName(name: string): name is CheckerName {
  return (CHECKER_NAMES as readonly string[]).includes(name);
}

/**
 * Register AST handlers for all enabled checkers.
 * Call this before running the visitor.
 */
export function setupAstCheckers(
  visitor: NodeIterator<FileAnalysis>,
  ctx: CheckerContext,
): void {
  for (const checker of ALL_CHECKERS) {
    if (!ctx.enabledCheckers.has(checker.name)) continue;
    checker.onAstTraversal?.(visitor, ctx);
  }
}

/**
 * Run all enabled checkers on the merged report.
 * Returns violations from cross-file checks.
 */
export function runMergedReportCheckers(
  report: FileAnalysis,
  enabledCheckers: Set<CheckerName>,
): Violation[] {
  const violations: Violation[] = [];
  for (const checker of ALL_CHECKERS) {
    if (!enabledCheckers.has(checker.name)) continue;
    if (!checker.onMergedReport) continue;
    violations.push(...checker.onMergedReport(report));
  }
  return violations;
}
