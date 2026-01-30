/**
 * TypeScript compiler API utilities for the reactivity analyzer.
 *
 * Loads project configs, creates Programs, and applies import-stub overlays.
 */

import path from "node:path";
import { existsSync } from "node:fs";
import ts from "typescript";

function toPosixPath(p: string): string {
  return p.split(path.sep).join(path.posix.sep);
}

export type ProjectConfig = {
  options: ts.CompilerOptions;
  fileNames: string[];
};

export function loadProjectConfig(
  tsMod: typeof import("typescript"),
  projectRoot: string,
): ProjectConfig {
  const configPath = path.join(projectRoot, "tsconfig.json");
  const readConfig = tsMod.readConfigFile(configPath, tsMod.sys.readFile);
  if (readConfig.error) {
    const msg = tsMod.formatDiagnosticsWithColorAndContext([readConfig.error], {
      getCurrentDirectory: () => projectRoot,
      getCanonicalFileName: (f: string) => toPosixPath(f),
      getNewLine: () => "\n",
    });
    throw new Error(msg);
  }

  const parsed = tsMod.parseJsonConfigFileContent(readConfig.config, tsMod.sys, projectRoot);
  return { options: parsed.options, fileNames: parsed.fileNames };
}

export function createAnalysisProgram(
  tsMod: typeof import("typescript"),
  args: { rootNames: string[]; compilerOptions: ts.CompilerOptions },
): ts.Program {
  const options: ts.CompilerOptions = {
    ...args.compilerOptions,
    noEmit: true,
  };
  options.incremental = false;
  delete (options as { tsBuildInfoFile?: unknown }).tsBuildInfoFile;

  return tsMod.createProgram({ rootNames: args.rootNames, options });
}

export function getDiagnostics(
  tsMod: typeof import("typescript"),
  program: ts.Program,
): readonly ts.Diagnostic[] {
  return tsMod.getPreEmitDiagnostics(program);
}

export function formatDiagnostics(
  tsMod: typeof import("typescript"),
  diags: readonly ts.Diagnostic[],
  projectRoot: string,
): string {
  return tsMod.formatDiagnosticsWithColorAndContext(diags, {
    getCurrentDirectory: () => projectRoot,
    getCanonicalFileName: (f: string) => toPosixPath(f),
    getNewLine: () => "\n",
  });
}

function findUp(startDir: string, relPath: string): string | null {
  let dir = startDir;
  for (;;) {
    const candidate = path.join(dir, relPath);
    if (existsSync(candidate)) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}

export function withImportStubs(
  projectRoot: string,
  options: ts.CompilerOptions,
): ts.CompilerOptions {
  const stubRoot = findUp(
    projectRoot,
    path.join("import-stubs", "@skipruntime", "core", "index.d.ts"),
  );
  if (!stubRoot) return options;

  const baseUrl = options.baseUrl ?? stubRoot;
  const paths = { ...(options.paths ?? {}) };
  const addPath = (key: string, value: string) => {
    if (!paths[key]) paths[key] = [value];
  };

  addPath("@skipruntime/core", "import-stubs/@skipruntime/core/index.d.ts");
  addPath("@skipruntime/helpers", "import-stubs/@skipruntime/helpers/index.d.ts");
  addPath("@skipruntime/server", "import-stubs/@skipruntime/server/index.d.ts");
  addPath("@skip-adapter/fastify", "import-stubs/@skip-adapter/fastify/index.d.ts");
  addPath("@fastify/*", "import-stubs/@fastify/*/index.d.ts");
  addPath("fastify", "import-stubs/fastify/index.d.ts");
  addPath("pino", "import-stubs/pino/index.d.ts");

  return { ...options, baseUrl, paths };
}

