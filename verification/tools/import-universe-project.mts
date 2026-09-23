/** Build an explicit import universe from a source checkout. Package entries,
 * TypeScript modules and workspace symlinks come from the files on disk; no
 * type definitions or module routes are handwritten in a sidecar. */
import { createHash } from "node:crypto";
import { lstatSync, readFileSync, readdirSync, realpathSync } from "node:fs";
import { dirname, join, relative, resolve, sep } from "node:path";
import { openText, type ImportUniverse } from "./fragment-parse.mts";

function text(value: unknown, what: string): string {
  if (typeof value !== "string" || !value) throw Error(`source project: missing ${what}`);
  return value;
}
function record(value: unknown, what: string): Record<string, unknown> {
  if (!value || typeof value !== "object" || Array.isArray(value))
    throw Error(`source project: invalid ${what}`);
  return value as Record<string, unknown>;
}
function digest(value: string): string {
  return createHash("sha256").update(value).digest("hex");
}

export function loadImportUniverseFromProject(directory: string): ImportUniverse {
  const root = realpathSync(resolve(directory));
  const inside = (absolute: string): string => {
    const path = relative(root, absolute).split(sep).join("/");
    if (path === ".." || path.startsWith("../") || path.startsWith("/"))
      throw Error(`source project: workspace link escapes ${root}`);
    return path;
  };
  const sourceFiles: string[] = [];
  const symlinks: string[] = [];
  const walk = (folder: string): void => {
    for (const entry of readdirSync(folder, { withFileTypes: true })) {
      if (["node_modules", "dist", ".git"].includes(entry.name)) continue;
      const path = join(folder, entry.name);
      if (entry.isSymbolicLink()) symlinks.push(path);
      else if (entry.isDirectory()) walk(path);
      else if (entry.isFile() && entry.name.endsWith(".ts")) sourceFiles.push(path);
    }
  };
  walk(join(root, "skipruntime-ts"));
  walk(join(root, "skiplang"));
  const moduleId = (path: string): string =>
    path.startsWith("skipruntime-ts/") ? path.slice("skipruntime-ts/".length) : path;
  const modules = sourceFiles.sort().map(absolute => {
    const bytes = readFileSync(absolute, "utf8");
    return { id: moduleId(inside(absolute)), sha256: digest(bytes), source: openText(absolute, bytes) };
  });
  const moduleIds = new Set(modules.map(module => module.id));
  if (moduleIds.size !== modules.length) throw Error("source project: duplicate module identity");
  const packages = new Map<string, string>();
  for (const entry of readdirSync(join(root, "skipruntime-ts"), { withFileTypes: true })) {
    if (!entry.isDirectory()) continue;
    const packageFile = join(root, "skipruntime-ts", entry.name, "package.json");
    try {
      if (!lstatSync(packageFile).isFile()) continue;
    } catch { continue; }
    const data: unknown = JSON.parse(readFileSync(packageFile, "utf8"));
    const packageJson = record(data, packageFile);
    if (typeof packageJson.name !== "string" || !packageJson.exports ||
        typeof packageJson.exports !== "object" || Array.isArray(packageJson.exports)) continue;
    const name = text(packageJson.name, `${packageFile} name`);
    const exports = record(packageJson.exports, `${packageFile} exports`);
    if (typeof exports["."] !== "string") continue;
    const entryPoint = text(exports["."], `${packageFile} main export`);
    if (!entryPoint.startsWith("./dist/") || !entryPoint.endsWith(".js")) continue;
    const id = `${entry.name}/${entryPoint.slice("./dist/".length, -3)}.ts`;
    // Packages compiled with a different rootDir (for example a native addon)
    // are outside this source layout. A client importing one is refused by the
    // resolver; unrelated packages need not block another client's universe.
    if (!moduleIds.has(id)) continue;
    if (packages.has(name)) throw Error(`source project: duplicate package ${name}`);
    packages.set(name, id);
  }
  const links = new Map<string, { virtual: string; canonical: string; source: string; sha256: string }>();
  const mappingSources = new Map<string, string>();
  for (const link of symlinks) {
    const sourcePath = inside(link);
    if (!sourcePath.startsWith("skipruntime-ts/")) continue;
    const canonicalPath = inside(realpathSync(link));
    const virtual = moduleId(sourcePath + "/index.ts");
    const canonical = moduleId(canonicalPath + "/index.ts");
    if (!moduleIds.has(canonical)) continue;
    const source = `symlink:${moduleId(sourcePath)}`;
    mappingSources.set(source, canonicalPath);
    links.set(virtual, { virtual, canonical, source, sha256: digest(canonicalPath) });
  }
  return { modules, config: { packages, links, mappingSources },
    tsconfigPath: join(root, "tsconfig.json") };
}
