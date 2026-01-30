/**
 * Generic checker infrastructure.
 *
 * Provides types and runner for analysis checkers.
 */

export type Violation = {
  checker: string;
  message: string;
  file: string;
  pos?: { line: number; col: number; endCol?: number };
  details?: Record<string, unknown>;
};

export type Checker<TReport> = (report: TReport) => Violation[];

export function runCheckers<TReport>(
  report: TReport,
  checkers: Checker<TReport>[],
): Violation[] {
  const violations: Violation[] = [];
  for (const checker of checkers) {
    violations.push(...checker(report));
  }
  return violations;
}
