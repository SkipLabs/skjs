/**
 * Skip-specific output formatting for the reactivity analyzer.
 */

import path from "node:path";
import type { FileAnalysis } from "./report.js";

export function printSummary(report: FileAnalysis, projectRoot: string): void {
  const rel = (f: string) => path.relative(projectRoot, f);

  console.log("Summary:");
  console.log(`  Service classes: ${report.serviceClasses.length}`);
  for (const s of report.serviceClasses) {
    console.log(`    - ${s.name} (${rel(s.file)}:${s.pos.line})`);
  }

  console.log(`  Mapper classes: ${report.mapperClasses.length}`);
  for (const m of report.mapperClasses) {
    console.log(`    - ${m.name} (${rel(m.file)}:${m.pos.line})`);
  }

  console.log(`  map() call sites: ${report.mapCalls.length}`);
}
