/**
 * Checker types for the reactivity analyzer.
 *
 * A checker can participate in two phases:
 * - AST traversal: register handlers that visit nodes and return violations
 * - Merged report: run after all files are analyzed and merged
 */

import type { AnalyzerContext, NodeIterator } from "../../infra/ast-inspection.js";
import type { Violation } from "../../infra/checker.js";
import type { FileAnalysis } from "../report.js";

/**
 * All known checker names as a const tuple for type safety.
 */
export const CHECKER_NAMES = [
  "no-non-null-assertion",
  "no-as-expression",
  "mapentry-values-toarray",
  "service-count",
  "service-members",
] as const;

export type CheckerName = (typeof CHECKER_NAMES)[number];

export type CheckerContext = AnalyzerContext<FileAnalysis> & {
  enabledCheckers: Set<CheckerName>;
};

/**
 * A checker that can detect violations in code.
 *
 * Checkers can participate in one or both phases:
 * - `onAstTraversal`: Called during per-file AST traversal. Register handlers
 *   on the visitor that return violations when visiting matching nodes.
 * - `onMergedReport`: Called after all files are analyzed and merged into a
 *   single report. Use for cross-file checks (e.g., "exactly one service class").
 */
export type Checker = {
  /** Unique identifier for this checker (used in --enable/--disable flags). */
  name: CheckerName;

  /**
   * Called during AST traversal phase (per-file).
   * Register node handlers on the visitor. Each handler receives a node and
   * returns violations found at that node.
   */
  onAstTraversal?: (visitor: NodeIterator<FileAnalysis>, ctx: CheckerContext) => void;

  /**
   * Called after all files are analyzed and merged into a single report.
   * Returns violations found in the merged report.
   */
  onMergedReport?: (report: FileAnalysis) => Violation[];
};
