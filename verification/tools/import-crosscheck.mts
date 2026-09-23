/** Check our source import graph against TypeScript's independently resolved
 * symbols. The resolver still chooses the graph; this only refuses disagreement. */
import { realpathSync } from "node:fs";
import { dirname } from "node:path";
import {
  API,
  SymbolFlags,
  type Checker,
  type Program,
} from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type {
  Identifier,
  Node,
  SourceFile,
  TypeReferenceNode,
  ExpressionWithTypeArguments,
} from "typescript/unstable/ast";
import type { ImportDocument, ResolvedImport, TypeDefinition } from "./imported-types.mts";
import type { ModuleSource } from "./module-resolve.mts";
import type { Span } from "./span.mts";

export class ImportMismatch extends Error {
  readonly clientSpan: Span;
  constructor(clientSpan: Span, message: string) {
    super(message);
    this.clientSpan = clientSpan;
  }
}

const key = (span: Span) => `${span[0]}:${span[1]}`;

function referenceAt(
  root: Node,
  source: SourceFile,
  span: Span,
): TypeReferenceNode | ExpressionWithTypeArguments | null {
  let found: TypeReferenceNode | ExpressionWithTypeArguments | null = null;
  const visit = (node: Node): void => {
    if (
      (ts.isTypeReferenceNode(node) || ts.isExpressionWithTypeArguments(node)) &&
      node.getStart(source) === span[0] &&
      node.end === span[1]
    )
      found = node;
    node.forEachChild(visit);
  };
  visit(root);
  return found;
}

function crossCheckProgram(
  client: SourceFile,
  roots: readonly ResolvedImport[],
  definitions: readonly TypeDefinition[],
  requiredSourceIds: readonly string[],
  typeDefinitionsOnly: boolean,
  modules: readonly ModuleSource[],
  program: Program,
  checker: Checker,
): void {
  const origin = roots[0]?.binding.span ?? [0, 0];
  const moduleById = new Map(modules.map((module) => [module.id, module]));
  const actualByPath = new Map<string, SourceFile>();
  for (const file of program.getSourceFileNames()) {
    const source = program.getSourceFile(file);
    if (source) actualByPath.set(realpathSync(file), source);
  }
  const sourceOf = (id: string, at: Span): SourceFile => {
    const module = moduleById.get(id);
    if (!module) throw new ImportMismatch(at, `module not supplied: ${id}`);
    const actual = actualByPath.get(realpathSync(module.source.fileName));
    if (!actual) throw new ImportMismatch(at, `TypeScript did not load ${id}`);
    return actual;
  };
  const compare = (
    id: string,
    span: Span,
    at: Span,
    name: string,
    identifier: Identifier,
    typeDefinitionOnly: boolean,
  ): void => {
    const symbol = checker.getSymbolAtLocation(identifier);
    if (!symbol)
      throw new ImportMismatch(at, `TypeScript found no symbol for ${name}`);
    // getAliasedSymbol requires Alias; a local recursive reference already
    // denotes its declaration and calling it on that symbol panics in tsgo.
    const target =
      symbol.flags & SymbolFlags.Alias
        ? checker.getAliasedSymbol(symbol)
        : symbol;
    if (checker.isUnknownSymbol(target))
      throw new ImportMismatch(
        at,
        `TypeScript found an unknown symbol for ${name}`,
      );
    if (target.declarations.length !== 1)
      throw new ImportMismatch(
        at,
        `TypeScript found ${target.declarations.length} declarations for ${name}`,
      );
    const node = target.declarations[0].resolve();
    if (!node || (typeDefinitionOnly &&
        !(ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node))))
      throw new ImportMismatch(
        at,
        `TypeScript target for ${name} is not ${typeDefinitionOnly ? "one type definition" : "one declaration"}`,
      );
    const actual = node.getSourceFile();
    const expected = moduleById.get(id);
    if (!expected) throw new ImportMismatch(at, `module not supplied: ${id}`);
    if (
      realpathSync(actual.fileName) !==
        realpathSync(expected.source.fileName) ||
      node.getStart(actual) !== span[0] ||
      node.end !== span[1]
    )
      throw new ImportMismatch(
        at,
        `import resolution differs for ${name}: TypeScript chose ${actual.fileName} [${node.getStart(actual)},${node.end}), resolver chose ${id} [${span[0]},${span[1]})`,
      );
  };

  for (const root of roots) {
    const binding = root.binding;
    const imported = client.statements
      .filter(ts.isImportDeclaration)
      .filter(
        (node) =>
          node.getStart(client) === binding.span[0] &&
          node.end === binding.span[1],
      );
    const names = imported.flatMap((node) =>
      node.importClause?.namedBindings &&
      ts.isNamedImports(node.importClause.namedBindings)
        ? [...node.importClause.namedBindings.elements]
        : [],
    );
    const specifier = names.find(
      (node) =>
        node.name.text === binding.local &&
        (node.propertyName?.text ?? node.name.text) === binding.imported,
    );
    if (!specifier)
      throw new ImportMismatch(
        binding.span,
        `TypeScript import binding missing: ${binding.local}`,
      );
    compare(
      root.declaration.module,
      root.declaration.span,
      binding.span,
      binding.local,
      specifier.name,
      typeDefinitionsOnly,
    );
  }

  for (const definition of definitions) {
    const id = definition.declaration.module;
    const source = sourceOf(id, origin);
    const declaration = source.statements.find(
      (node) =>
        (ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)) &&
        node.getStart(source) === definition.declaration.span[0] &&
        node.end === definition.declaration.span[1],
    );
    if (!declaration)
      throw new ImportMismatch(
        origin,
        `TypeScript did not load type definition ${id}#${definition.declaration.name}`,
      );
    for (const reference of definition.references) {
      const node = referenceAt(declaration, source, reference.span);
      const identifier = node && (ts.isTypeReferenceNode(node) ? node.typeName : node.expression);
      if (!identifier || !ts.isIdentifier(identifier))
        throw new ImportMismatch(
          origin,
          `TypeScript reference missing at ${id} [${key(reference.span)})`,
        );
      compare(
        reference.target.module,
        reference.target.span,
        origin,
        `${id}#${reference.name} [${key(reference.span)})`,
        identifier,
        true,
      );
    }
  }

  // Compare every supplied module TypeScript loaded, including reexport
  // candidates it examined but which did not become graph equations. Every
  // required route or equation source must also have been loaded. One direct
  // text comparison per module is enough; stored hashes carry no authority.
  const compared = new Set<string>();
  for (const module of modules) {
    const actual = actualByPath.get(realpathSync(module.source.fileName));
    if (!actual) continue;
    compared.add(module.id);
    if (actual.getFullText() !== module.source.getFullText())
      throw new ImportMismatch(
        origin,
        `TypeScript source bytes differ for ${module.id}`,
      );
  }
  for (const id of requiredSourceIds)
    if (!compared.has(id))
      throw new ImportMismatch(origin,
        `TypeScript did not load ${id}`);
}

function crossCheckSource(
  client: SourceFile,
  roots: readonly ResolvedImport[],
  definitions: readonly TypeDefinition[],
  requiredSourceIds: readonly string[],
  typeDefinitionsOnly: boolean,
  modules: readonly ModuleSource[],
  resolutionFile: string,
  tsconfigPath?: string,
): void {
  // A separate compiler has no parser-side in-memory source overrides. It
  // resolves the actual project and bytes on disk, independently of ours.
  const api = new API({ cwd: dirname(resolutionFile) });
  try {
    const snapshot = api.updateSnapshot({ openFiles: [resolutionFile],
      ...(tsconfigPath ? { openProjects: [tsconfigPath] } : {}) });
    const project = tsconfigPath
      ? snapshot.getProject(tsconfigPath)
      : snapshot.getDefaultProjectForFile(resolutionFile);
    if (!project)
      throw new ImportMismatch(
        roots[0]?.binding.span ?? [0, 0],
        `TypeScript did not open ${resolutionFile}`,
      );
    if (!project.configFileName || !project.compilerOptions.strict)
      throw new ImportMismatch(
        roots[0]?.binding.span ?? [0, 0],
        `TypeScript did not load a strict tsconfig for ${resolutionFile}`,
      );
    const checkedClient = project.program.getSourceFile(resolutionFile);
    if (!checkedClient)
      throw new ImportMismatch(
        roots[0]?.binding.span ?? [0, 0],
        `TypeScript did not load ${resolutionFile}`,
      );
    crossCheckProgram(
      checkedClient,
      roots,
      definitions,
      requiredSourceIds,
      typeDefinitionsOnly,
      modules,
      project.program,
      project.checker,
    );
    if (checkedClient.getFullText() !== client.getFullText())
      throw new ImportMismatch(
        roots[0]?.binding.span ?? [0, 0],
        "TypeScript client source bytes differ",
      );
  } finally {
    api.close();
  }
}

export function crossCheckImports(
  client: SourceFile,
  document: ImportDocument,
  modules: readonly ModuleSource[],
  resolutionFile: string,
  tsconfigPath?: string,
): void {
  crossCheckSource(client, document.roots, document.definitions,
    document.sources.map(source => source.module), true, modules,
    resolutionFile, tsconfigPath);
}

/** Check identities for declarations whose contracts the fragment cannot yet
 * interpret. This is a provenance check, never a typing certificate. */
export function crossCheckResolvedBindings(
  client: SourceFile,
  roots: readonly ResolvedImport[],
  modules: readonly ModuleSource[],
  resolutionFile: string,
  tsconfigPath?: string,
): void {
  const required = roots.flatMap(root => [root.declaration.module,
    ...root.route.map(step => step.module)]);
  crossCheckSource(client, roots, [], required, false, modules,
    resolutionFile, tsconfigPath);
}
