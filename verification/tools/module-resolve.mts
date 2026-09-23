/** Resolve a named import to the declaration it actually denotes. This is
 * source provenance, not a proof of the imported declaration's contract. The
 * caller supplies an explicit, fingerprinted module universe: an absent or
 * ambiguous edge is an error, never an ambient TypeScript declaration. */
import { createHash } from "node:crypto";
import { posix } from "node:path";
import * as ts from "typescript/unstable/ast";
import type { SourceFile } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { moduleEdges, type ModuleEdge } from "./module-deps.mts";

export type ModuleSource = {
  id: string;
  sha256: string;
  source: SourceFile;
};
export type DeclarationIdentity = {
  module: string;
  name: string;
  span: Span;
  capability: "type" | "value" | "both";
};
export type ResolvedImport = {
  binding: ModuleEdge;
  declaration: DeclarationIdentity;
  /** Every file whose bytes determined the route, including the final one. */
  route: { module: string; sha256: string }[];
};

function exported(statement: { modifiers?: readonly { kind: number }[] }): boolean {
  return statement.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) === true;
}

function directExport(source: SourceFile, name: string): DeclarationIdentity | null {
  for (const statement of source.statements) {
    if (!(ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement) ||
      ts.isFunctionDeclaration(statement) || ts.isVariableStatement(statement) ||
      ts.isClassDeclaration(statement) || ts.isEnumDeclaration(statement))) continue;
    if (!exported(statement)) continue;
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

export function resolveNamedImports(
  client: SourceFile,
  modules: readonly ModuleSource[],
  packages: ReadonlyMap<string, string>,
): ResolvedImport[] {
  const universe = new Map<string, ModuleSource>();
  for (const module of modules) {
    if (universe.has(module.id)) throw Error(`duplicate module ${module.id}`);
    if (createHash("sha256").update(module.source.getFullText()).digest("hex") !== module.sha256)
      throw Error(`module fingerprint differs: ${module.id}`);
    universe.set(module.id, module);
  }
  const target = (from: string | null, specifier: string): string => {
    if (!specifier.startsWith(".")) {
      const id = packages.get(specifier);
      if (!id) throw Error(`unresolved package ${specifier}`);
      return id;
    }
    if (!from) throw Error(`relative import without module identity: ${specifier}`);
    const path = posix.normalize(posix.join(posix.dirname(from), specifier));
    if (!path.endsWith(".js")) throw Error(`unsupported relative specifier ${specifier}`);
    return path.slice(0, -3) + ".ts";
  };
  const visit = (id: string, name: string, seen: Set<string>): {
    declaration: DeclarationIdentity;
    route: ResolvedImport["route"];
  } | null => {
    const key = `${id}#${name}`;
    if (seen.has(key)) throw Error(`cyclic reexport ${key}`);
    const module = universe.get(id);
    if (!module) throw Error(`module not supplied: ${id}`);
    const route = [{ module: id, sha256: module.sha256 }];
    const direct = directExport(module.source, name);
    if (direct) return { declaration: { ...direct, module: id }, route };
    const outgoing = moduleEdges(module.source).filter(e =>
      e.kind === "reexport" && (e.local === name || e.local === "*"));
    const answers: NonNullable<ReturnType<typeof visit>>[] = [];
    for (const edge of outgoing) {
      if (edge.imported === "*" && edge.local !== "*")
        throw Error(`unsupported namespace reexport ${key}`);
      const next = target(id, edge.specifier);
      const answer = visit(next, edge.local === "*" ? name : edge.imported,
        new Set([...seen, key]));
      if (answer)
        answers.push({ declaration: answer.declaration, route: [...route, ...answer.route] });
      else if (edge.local !== "*") throw Error(`broken named reexport ${key}`);
    }
    if (answers.length > 1) throw Error(`ambiguous export ${key}`);
    if (answers.length === 1) return answers[0];
    return null;
  };
  return moduleEdges(client).filter(e => e.kind === "import").map(binding => {
    if (!binding.imported || binding.imported === "*" || binding.imported === "default")
      throw Error(`unsupported import form at ${binding.span[0]}`);
    const found = visit(target(null, binding.specifier), binding.imported, new Set());
    if (!found) throw Error(`export not found: ${binding.specifier}#${binding.imported}`);
    if (!binding.typeOnly && found.declaration.capability === "type")
      throw Error(`value import resolves to type-only declaration: ${binding.imported}`);
    return { binding, ...found };
  });
}
