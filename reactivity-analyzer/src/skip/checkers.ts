/**
 * Skip-specific checker entrypoint for the reactivity analyzer.
 */

import type { Violation } from "../infra/checker.js";
import type { FileAnalysis } from "./report.js";
import {
  DEFAULT_ENABLED_CHECKERS,
  runMergedReportCheckers,
  type CheckerName,
} from "./checkers/index.js";

export type { Violation };

export function runCheckers(
  report: FileAnalysis,
  enabledCheckers: Set<CheckerName> = new Set(DEFAULT_ENABLED_CHECKERS),
): Violation[] {
  return runMergedReportCheckers(report, enabledCheckers);
}
