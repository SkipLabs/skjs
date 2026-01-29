#!/usr/bin/env node
/**
 * skcheck - Static analyzer for Skip reactive services
 */

import path from "node:path";
import fs from "node:fs";
import { spawn } from "node:child_process";
import * as ts from "typescript";
import {
  createAnalysisProgram,
  formatDiagnostics,
  getDiagnostics,
  loadProjectConfig,
  withImportStubs,
} from "./infra/tsc.js";
import { formatCodeFrame } from "./infra/code-frame.js";
import { analyzeProgram, type AnalysisResult } from "./skip/collectors.js";
import { mergeFileAnalyses, type FileAnalysis } from "./skip/report.js";
import { runCheckers, type Violation } from "./skip/checkers.js";
import {
  ALL_CHECKER_NAMES,
  DEFAULT_ENABLED_CHECKERS,
  isKnownCheckerName,
  type CheckerName,
} from "./skip/checkers/index.js";
import { printSummary } from "./skip/output.js";

function mergeAnalysisResults(results: AnalysisResult[]): { merged: FileAnalysis; violations: Violation[] } {
  const analyses = results.map((r) => r.analysis);
  const violations = results.flatMap((r) => r.violations);
  return { merged: mergeFileAnalyses(analyses), violations };
}

const VERSION = "0.0.1";

const CHECKER_LIST = ALL_CHECKER_NAMES.join(", ");

const LEGACY_CHECKER_ALIASES: Record<string, CheckerName[]> = {
  "no-as-expression": [
    "no-as-expression-from-json",
    "no-as-expression-necessary",
    "no-as-expression-unnecessary",
  ],
};

const HELP = `
skcheck - Static analyzer for Skip reactive services

USAGE
  skcheck [options]
  skcheck all [options]
  skcheck build

COMMANDS
  all                Analyze all generated-examples projects
  build              Rebuild skcheck (runs npm install && npm run build)

OPTIONS
  --project <path>   Project root containing tsconfig.json (default: .)
  --parallel <n>     Number of parallel analyses (default: 8, for 'all' command)
  --enable <list>    Enable only these checkers (comma-separated)
  --disable <list>   Disable these checkers (comma-separated)
  --verbose          Print non-error output
  --help             Show this help message
  --version          Show version

CHECKERS
  ${CHECKER_LIST}

EXAMPLES
  skcheck --project ../my-service              # Analyze a single project
  skcheck --disable no-as-expression-from-json,no-as-expression-necessary,no-as-expression-unnecessary  # Skip as-expression checks
  skcheck --enable service-count,service-members  # Only run service checks
  skcheck all                                  # Analyze all generated-examples
  skcheck all --parallel 8 --verbose           # With more parallelism + output
`.trim();

function getArgValue(flag: string): string | null {
  const argv = process.argv;
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === flag && i + 1 < argv.length) return String(argv[i + 1]);
  }
  return null;
}

function hasFlag(flag: string): boolean {
  return process.argv.includes(flag);
}

function getCommand(): string | null {
  const arg = process.argv[2];
  if (arg && !arg.startsWith("-")) return arg;
  return null;
}

function expandCheckerName(name: string): CheckerName[] | null {
  if (isKnownCheckerName(name)) return [name];
  return LEGACY_CHECKER_ALIASES[name] ?? null;
}

function parseEnabledCheckers(): Set<CheckerName> {
  const enableArg = getArgValue("--enable");
  const disableArg = getArgValue("--disable");

  let enabled = new Set<CheckerName>(DEFAULT_ENABLED_CHECKERS);

  if (enableArg) {
    const names = enableArg.split(",").map((s) => s.trim());
    enabled = new Set<CheckerName>();
    for (const name of names) {
      const expanded = expandCheckerName(name);
      if (expanded) {
        for (const checker of expanded) enabled.add(checker);
      } else {
        console.error(`Unknown checker: ${name}`);
        console.error(`Available checkers: ${CHECKER_LIST}`);
        process.exit(1);
      }
    }
  }

  if (disableArg) {
    const names = disableArg.split(",").map((s) => s.trim());
    for (const name of names) {
      const expanded = expandCheckerName(name);
      if (expanded) {
        for (const checker of expanded) enabled.delete(checker);
      } else {
        console.error(`Unknown checker: ${name}`);
        console.error(`Available checkers: ${CHECKER_LIST}`);
        process.exit(1);
      }
    }
  }

  return enabled;
}

function printViolationSummary(violations: Violation[]): void {
  const counts = new Map<string, number>();
  for (const v of violations) {
    counts.set(v.checker, (counts.get(v.checker) || 0) + 1);
  }

  console.error(`Found ${violations.length} violation(s):`);
  for (const [checker, count] of Array.from(counts.entries()).sort()) {
    console.error(`  ${checker}: ${count}`);
  }
  console.error("");
}

function findGeneratedExamplesRoot(): string | null {
  // Look for generated-examples relative to this file's location
  // This file is at reactivity-analyzer/dist/cli.js (sibling to generated-examples)
  const thisDir = path.dirname(new URL(import.meta.url).pathname);
  const repoRoot = path.resolve(thisDir, "..", "..");
  const candidate = path.join(repoRoot, "generated-examples");
  if (fs.existsSync(candidate)) {
    return candidate;
  }
  // Fallback: look from cwd
  const fromCwd = path.join(process.cwd(), "generated-examples");
  if (fs.existsSync(fromCwd)) {
    return fromCwd;
  }
  return null;
}

function findProjects(rootDir: string): string[] {
  const projects: string[] = [];
  const excluded = new Set(["node_modules", "dist", "dist-analysis", ".git", "reactivity-analyzer"]);

  function walk(dir: string): void {
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }

    for (const entry of entries) {
      if (excluded.has(entry.name)) continue;
      const fullPath = path.join(dir, entry.name);

      if (entry.isDirectory()) {
        const tsconfig = path.join(fullPath, "tsconfig.json");
        if (fs.existsSync(tsconfig)) {
          projects.push(fullPath);
        } else {
          walk(fullPath);
        }
      }
    }
  }

  walk(rootDir);
  return projects;
}

type ProjectResult = {
  project: string;
  success: boolean;
  violations: Violation[];
  output?: string;
  error?: string;
};

async function analyzeProjectAsync(projectPath: string): Promise<ProjectResult> {
  return new Promise((resolve) => {
    const args = ["--project", projectPath, "--no-summary"];
    if (hasFlag("--verbose")) args.push("--verbose");
    const enableArg = getArgValue("--enable");
    const disableArg = getArgValue("--disable");
    if (enableArg) args.push("--enable", enableArg);
    if (disableArg) args.push("--disable", disableArg);

    const canColorize =
      process.stderr.isTTY && process.env.NO_COLOR === undefined;
    const env = canColorize
      ? { ...process.env, FORCE_COLOR: "1" }
      : process.env;

    const proc = spawn(process.argv[0]!, [process.argv[1]!, ...args], {
      stdio: ["ignore", "pipe", "pipe"],
      env,
    });

    let stdout = "";
    let stderr = "";
    proc.stdout?.on("data", (data) => (stdout += data));
    proc.stderr?.on("data", (data) => (stderr += data));

    proc.on("close", (code) => {
      resolve({
        project: projectPath,
        success: code === 0,
        violations: [],
        output: stdout,
        error: code !== 0 ? stderr || stdout : undefined,
      });
    });

    proc.on("error", (err) => {
      resolve({
        project: projectPath,
        success: false,
        violations: [],
        error: err.message,
      });
    });
  });
}

async function runAll(rootDir: string, parallel: number, verbose: boolean): Promise<void> {
  // Validate checker names early, before spawning child processes
  parseEnabledCheckers();

  const projects = findProjects(rootDir);

  if (projects.length === 0) {
    console.log(`No projects found under ${rootDir}`);
    return;
  }

  // Always show progress info
  console.log(`Found ${projects.length} project(s) under ${rootDir}`);
  console.log(`Running with parallelism: ${parallel}\n`);

  const results: ProjectResult[] = [];
  const pending = [...projects];

  async function runBatch(): Promise<void> {
    const batch: Promise<ProjectResult>[] = [];
    const batchProjects: string[] = [];
    while (batch.length < parallel && pending.length > 0) {
      const project = pending.shift()!;
      batchProjects.push(project);
      batch.push(analyzeProjectAsync(project));
    }

    // Always show which projects are being analyzed
    for (const project of batchProjects) {
      const relPath = path.relative(rootDir, project);
      console.log(`Analyzing: ${relPath}`);
    }

    const batchResults = await Promise.all(batch);
    results.push(...batchResults);

    // Print detailed output only in verbose mode
    if (verbose) {
      for (const result of batchResults) {
        const relPath = path.relative(rootDir, result.project);
        console.log(`--- ${relPath} ---`);
        if (result.output) {
          console.log(result.output.trimEnd());
        }
        console.log();
      }
    }
  }

  while (pending.length > 0) {
    await runBatch();
  }

  // Aggregate violation counts from all projects
  const violationCounts = new Map<string, number>();
  let totalViolations = 0;
  const checkerPattern = /error \[([^\]]+)\]/g;

  for (const r of results) {
    if (r.error) {
      for (const match of r.error.matchAll(checkerPattern)) {
        const checker = match[1]!;
        violationCounts.set(checker, (violationCounts.get(checker) || 0) + 1);
        totalViolations++;
      }
    }
  }

  // Summary
  const failed = results.filter((r) => !r.success);
  const passed = results.filter((r) => r.success);

  console.log(`\n${"=".repeat(60)}`);
  console.log(`Results: ${passed.length} passed, ${failed.length} failed`);

  if (totalViolations > 0) {
    console.log(`\nFound ${totalViolations} violation(s) across all projects:`);
    for (const [checker, count] of Array.from(violationCounts.entries()).sort()) {
      console.log(`  ${checker}: ${count}`);
    }
  }
  console.log("");

  if (failed.length > 0) {
    console.log("Failed projects:");
    for (const r of failed) {
      console.log(`  - ${path.relative(rootDir, r.project)}`);
      if (r.error) {
        for (const line of r.error.trim().split("\n")) {
          console.log(`      ${line}`);
        }
      }
    }
    process.exit(1);
  }
}

export function main(): void {
  if (hasFlag("--help") || hasFlag("-h")) {
    console.log(HELP);
    process.exit(0);
  }

  if (hasFlag("--version") || hasFlag("-v")) {
    console.log(VERSION);
    process.exit(0);
  }

  const command = getCommand();

  if (command === "all") {
    const parallelArg = getArgValue("--parallel");
    const verbose = hasFlag("--verbose");
    const rootDir = findGeneratedExamplesRoot();
    const parallel = parallelArg ? parseInt(parallelArg, 10) : 8;

    if (!rootDir) {
      console.error("Could not find generated-examples directory.");
      process.exit(1);
    }

    runAll(rootDir, parallel, verbose).catch((err) => {
      console.error(err);
      process.exit(1);
    });
    return;
  }

  const projectArg = getArgValue("--project");
  const verbose = hasFlag("--verbose");
  const projectRoot = projectArg ? path.resolve(projectArg) : process.cwd();
  const enabledCheckers = parseEnabledCheckers();

  const config = loadProjectConfig(ts, projectRoot);
  const options = withImportStubs(projectRoot, config.options);
  const program = createAnalysisProgram(ts, {
    rootNames: config.fileNames,
    compilerOptions: options,
  });

  const diagnostics = getDiagnostics(ts, program);
  if (diagnostics.length > 0) {
    console.error("Typecheck failed:\n");
    console.error(formatDiagnostics(ts, diagnostics, projectRoot));
    process.exit(1);
  }

  // Always show what we're analyzing
  console.log(`Analyzing ${config.fileNames.length} file(s)...`);

  // Analyze all source files
  const results: AnalysisResult[] = [];
  for (const fileName of config.fileNames) {
    const sf = program.getSourceFile(fileName);
    if (!sf) continue;
    // Skip declaration files
    if (sf.isDeclarationFile) continue;
    const result = analyzeProgram(ts, { program, sourceFile: sf }, { enabledCheckers });
    results.push(result);
  }

  const { merged, violations: directViolations } = mergeAnalysisResults(results);
  const checkerViolations = runCheckers(merged, enabledCheckers);
  const violations = [...directViolations, ...checkerViolations];

  if (verbose) printSummary(merged, projectRoot);

  if (violations.length > 0) {
    // Print summary first (unless --no-summary is passed)
    if (!hasFlag("--no-summary")) {
      printViolationSummary(violations);
    }

    // Then print detailed violations
    for (const v of violations) {
      const line = v.pos ? v.pos.line : 1;
      const col = v.pos ? v.pos.col : 1;
      const endCol = v.pos && typeof v.pos.endCol === "number" ? v.pos.endCol : undefined;
      const relFile = path.relative(projectRoot, v.file);
      console.error(`${relFile}:${line}:${col}: error [${v.checker}] ${v.message}`);
      const highlightLength = endCol ? Math.max(1, endCol - col) : 1;
      const frame = formatCodeFrame({ filePath: v.file, line, col, highlightLength });
      if (frame) {
        console.error(frame);
      }
      console.error("");
    }
    process.exit(1);
  }
}

main();
