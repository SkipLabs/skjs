/** Resolve a named import or configured global to its source declaration.
 * This is provenance, not a proof of the declaration's contract. The caller
 * supplies an explicit source universe: an absent or ambiguous edge is an
 * error, never an unexamined ambient TypeScript declaration. */
import { createHash } from "node:crypto";
import { posix } from "node:path";
import * as ts from "typescript/unstable/ast";
import type { SourceFile } from "typescript/unstable/ast";
import { moduleEdges } from "./module-deps.mts";
import type { DeclarationIdentity, MappingStep, ResolvedImport } from "./imported-types.mts";
export type { DeclarationIdentity, MappingStep, ResolvedImport } from "./imported-types.mts";

export type ModuleSource = {
  id: string;
  sha256: string;
  source: SourceFile;
};
export type ResolutionConfig = {
  packages: ReadonlyMap<string, string>;
  /** Declaration files loaded as globals by the configured TypeScript project. */
  globals: ReadonlySet<string>;
  /** Exact workspace links, justified by a pinned file such as prebuild.mjs. */
  links: ReadonlyMap<string, MappingStep>;
  mappingSources: ReadonlyMap<string, string>;
};

/** Resolve a bare type name against configured global declaration files. The
 * source scan chooses the candidate; the separate checker must confirm its
 * exact declaration identity before the closure can be used. */
export function resolveGlobalType(
  name: string,
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
): { declaration: DeclarationIdentity; route: ResolvedImport["route"] } | null {
  const universe = new Map(modules.map(module => [module.id, module]));
  const found: { declaration: DeclarationIdentity; route: ResolvedImport["route"] }[] = [];
  for (const id of config.globals) {
    const module = universe.get(id);
    if (!module) throw Error(`global module not supplied: ${id}`);
    for (const statement of module.source.statements) {
      if (!(ts.isTypeAliasDeclaration(statement) || ts.isInterfaceDeclaration(statement)) ||
          statement.name.text !== name) continue;
      found.push({ declaration: { module: id, name,
        span: [statement.getStart(module.source), statement.end], capability: "type" },
        route: [{ module: id, sha256: module.sha256 }] });
    }
  }
  if (found.length > 1) throw Error(`ambiguous global type ${name}`);
  return found[0] ?? null;
}

function exported(statement: { modifiers?: readonly { kind: number }[] }): boolean {
  return statement.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) === true;
}

function declaration(source: SourceFile, name: string, onlyExported: boolean): DeclarationIdentity | null {
  for (const statement of source.statements) {
    if (!(ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement) ||
      ts.isFunctionDeclaration(statement) || ts.isVariableStatement(statement) ||
      ts.isClassDeclaration(statement) || ts.isEnumDeclaration(statement))) continue;
    if (onlyExported && !exported(statement)) continue;
    const capability = ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)
      ? "type" : ts.isFunctionDeclaration(statement) || ts.isVariableStatement(statement)
        ? "value" : "both";
    if (ts.isVariableStatement(statement)) {
      for (const declaration of statement.declarationList.declarations)
        if (ts.isIdentifier(declaration.name) && declaration.name.text === name)
          return { module: "", name, span: [declaration.getStart(source), declaration.end], capability };
    } else if (statement.name && ts.isIdentifier(statement.name) && statement.name.text === name)
      return { module: "", name, span: [statement.getStart(source), statement.end], capability };
  }
  return null;
}

function localExports(source: SourceFile, name: string): {
  local: string;
  typeOnly: boolean;
}[] {
  const out: { local: string; typeOnly: boolean }[] = [];
  for (const statement of source.statements) {
    if (!ts.isExportDeclaration(statement) || statement.moduleSpecifier ||
        !statement.exportClause || !ts.isNamedExports(statement.exportClause)) continue;
    for (const item of statement.exportClause.elements)
      if (item.name.text === name)
        out.push({ local: item.propertyName?.text ?? item.name.text,
          typeOnly: statement.isTypeOnly || item.isTypeOnly });
  }
  return out;
}

function restrict(capability: DeclarationIdentity["capability"], typeOnly: boolean):
  DeclarationIdentity["capability"] {
  if (!typeOnly) return capability;
  if (capability === "value") throw Error("type-only export has no type declaration");
  return "type";
}

function resolveImports(
  client: SourceFile,
  importer: string | null,
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
  onlyLocal: string | null,
): ResolvedImport[] {
  const universe = new Map<string, ModuleSource>();
  for (const module of modules) {
    if (universe.has(module.id)) throw Error(`duplicate module ${module.id}`);
    universe.set(module.id, module);
  }
  for (const [virtual, mapping] of config.links) {
    if (mapping.virtual !== virtual)
      throw Error(`mapping key differs from virtual path: ${virtual}`);
    const source = config.mappingSources.get(mapping.source);
    if (source === undefined ||
        createHash("sha256").update(source).digest("hex") !== mapping.sha256)
      throw Error(`mapping fingerprint differs: ${mapping.source}`);
  }
  const target = (from: string | null, specifier: string): {
    id: string;
    mappings: MappingStep[];
  } => {
    if (!specifier.startsWith(".")) {
      const id = config.packages.get(specifier);
      if (!id) throw Error(`unresolved package ${specifier}`);
      return { id, mappings: [] };
    }
    if (!from) throw Error(`relative import without module identity: ${specifier}`);
    const path = posix.normalize(posix.join(posix.dirname(from), specifier));
    if (!path.endsWith(".js")) throw Error(`unsupported relative specifier ${specifier}`);
    const virtual = path.slice(0, -3) + ".ts";
    const mapped = config.links.get(virtual);
    return mapped ? { id: mapped.canonical, mappings: [mapped] } :
      { id: virtual, mappings: [] };
  };
  type Found = {
    declaration: DeclarationIdentity;
    route: ResolvedImport["route"];
    mappings: MappingStep[];
    available: DeclarationIdentity["capability"];
  };
  const visit = (id: string, name: string, seen: Set<string>): Found | null => {
    const key = `${id}#${name}`;
    if (seen.has(key)) throw Error(`cyclic reexport ${key}`);
    const module = universe.get(id);
    if (!module) throw Error(`module not supplied: ${id}`);
    const route = [{ module: id, sha256: module.sha256 }];
    const direct = declaration(module.source, name, true);
    if (direct) return { declaration: { ...direct, module: id }, route,
      mappings: [], available: direct.capability };
    const answers: Found[] = [];
    for (const edge of localExports(module.source, name)) {
      const local = declaration(module.source, edge.local, false);
      if (local) {
        answers.push({ declaration: { ...local, module: id }, route,
          mappings: [], available: restrict(local.capability, edge.typeOnly) });
        continue;
      }
      const imports = moduleEdges(module.source).filter(e =>
        e.kind === "import" && e.local === edge.local);
      if (imports.length !== 1) throw Error(`unresolved local export ${key}`);
      const binding = imports[0];
      if (!binding.imported || binding.imported === "*" || binding.imported === "default")
        throw Error(`unsupported local export ${key}`);
      const next = target(id, binding.specifier);
      const found = visit(next.id, binding.imported, new Set([...seen, key]));
      if (!found) throw Error(`broken local export ${key}`);
      answers.push({ ...found, route: [...route, ...found.route],
        mappings: [...next.mappings, ...found.mappings],
        available: restrict(found.available, edge.typeOnly || binding.typeOnly) });
    }
    const outgoing = moduleEdges(module.source).filter(e =>
      e.kind === "reexport" && (e.local === name || e.local === "*"));
    for (const edge of outgoing) {
      if (edge.imported === "*" && edge.local !== "*")
        throw Error(`unsupported namespace reexport ${key}`);
      const next = target(id, edge.specifier);
      const answer = visit(next.id, edge.local === "*" ? name : edge.imported,
        new Set([...seen, key]));
      if (answer)
        answers.push({ ...answer, route: [...route, ...answer.route],
          mappings: [...next.mappings, ...answer.mappings],
          available: restrict(answer.available, edge.typeOnly) });
      else if (edge.local !== "*") throw Error(`broken named reexport ${key}`);
    }
    if (answers.length > 1) throw Error(`ambiguous export ${key}`);
    if (answers.length === 1) return answers[0];
    return null;
  };
  return moduleEdges(client).filter(e => e.kind === "import" &&
    (onlyLocal === null || e.local === onlyLocal)).map(binding => {
    if (!binding.imported || binding.imported === "*" || binding.imported === "default")
      throw Error(`unsupported import form at ${binding.span[0]}`);
    const entry = target(importer, binding.specifier);
    const found = visit(entry.id, binding.imported, new Set());
    if (!found) throw Error(`export not found: ${binding.specifier}#${binding.imported}`);
    if (!binding.typeOnly && found.available === "type")
      throw Error(`value import resolves to type-only declaration: ${binding.imported}`);
    return { binding, ...found, available: restrict(found.available, binding.typeOnly),
      mappings: [...entry.mappings, ...found.mappings] };
  });
}

export function resolveNamedImports(
  client: SourceFile,
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
): ResolvedImport[] {
  return resolveImports(client, null, modules, config, null);
}

/** Resolve just one local imported name. Dependency collection must not be
 * blocked by unrelated imports elsewhere in the declaration's source file. */
export function resolveModuleImport(
  moduleId: string,
  localName: string,
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
): ResolvedImport | null {
  const module = modules.find(m => m.id === moduleId);
  if (!module) throw Error(`module not supplied: ${moduleId}`);
  const found = resolveImports(module.source, moduleId, modules, config, localName);
  if (found.length > 1) throw Error(`ambiguous local import ${moduleId}#${localName}`);
  return found[0] ?? null;
}
