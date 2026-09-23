/** The reachable *source declaration* closure of an imported type. This is a
 * finite provenance graph, not yet an interpretation of those declarations as
 * semantic types. Unsupported binding forms fail instead of disappearing. */
import { createHash } from "node:crypto";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile, TypeAliasDeclaration } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { resolveModuleImport, type DeclarationIdentity, type MappingStep,
  type ModuleSource, type ResolutionConfig, type ResolvedImport } from "./module-resolve.mts";

export type Reference = {
  name: string;
  span: Span;
  arguments: Span[];
  target: DeclarationIdentity;
  route: ResolvedImport["route"];
  mappings: MappingStep[];
};
export type TypeDefinition = {
  declaration: DeclarationIdentity;
  sha256: string;
  parameters: { name: string; span: Span }[];
  body: Span;
  references: Reference[];
};
export type TypeClosure = { root: ResolvedImport; definitions: TypeDefinition[] };

function alias(source: SourceFile, identity: DeclarationIdentity): TypeAliasDeclaration {
  const matches = source.statements.filter(statement =>
    ts.isTypeAliasDeclaration(statement) && statement.name.text === identity.name &&
    statement.getStart(source) === identity.span[0] && statement.end === identity.span[1]);
  if (matches.length !== 1 || !ts.isTypeAliasDeclaration(matches[0]))
    throw Error(`type alias identity not found: ${identity.module}#${identity.name}`);
  return matches[0];
}

function localAlias(source: SourceFile, moduleId: string, name: string):
  DeclarationIdentity | null {
  const matches = source.statements.filter(statement =>
    ts.isTypeAliasDeclaration(statement) && statement.name.text === name);
  if (matches.length > 1) throw Error(`ambiguous local alias ${moduleId}#${name}`);
  const found = matches[0];
  if (!found) return null;
  return { module: moduleId, name,
    span: [found.getStart(source), found.end], capability: "type" };
}

export function collectTypeClosure(
  root: ResolvedImport,
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
): TypeClosure {
  if (root.available === "value") throw Error("value import is not a type root");
  const universe = new Map<string, ModuleSource>();
  for (const module of modules) {
    if (universe.has(module.id)) throw Error(`duplicate module ${module.id}`);
    if (createHash("sha256").update(module.source.getFullText()).digest("hex") !== module.sha256)
      throw Error(`module fingerprint differs: ${module.id}`);
    universe.set(module.id, module);
  }
  const sourceOf = (id: string): SourceFile => {
    const module = universe.get(id);
    if (!module) throw Error(`module not supplied: ${id}`);
    return module.source;
  };
  const queue: DeclarationIdentity[] = [root.declaration];
  const seen = new Set<string>();
  const definitions: TypeDefinition[] = [];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const identity = queue[cursor];
    if (!identity) throw Error("missing queued declaration");
    const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const module = universe.get(identity.module);
    if (!module) throw Error(`module not supplied: ${identity.module}`);
    const source = module.source;
    const node = alias(source, identity);
    const parameters = node.typeParameters?.map(parameter => {
      const span: Span = [parameter.getStart(source), parameter.end];
      return { name: parameter.name.text, span };
    }) ?? [];
    if (new Set(parameters.map(p => p.name)).size !== parameters.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
    const bound = new Set(parameters.map(p => p.name));
    const references: Reference[] = [];
    const visit = (part: Node): void => {
      if (ts.isImportTypeNode(part) || ts.isTypeQueryNode(part) ||
          ts.isConditionalTypeNode(part) || ts.isMappedTypeNode(part) ||
          ts.isInferTypeNode(part))
        throw Error(`unsupported type binding in ${identity.module}#${identity.name}`);
      if (ts.isTypeReferenceNode(part)) {
        if (!ts.isIdentifier(part.typeName))
          throw Error(`qualified type reference in ${identity.module}#${identity.name}`);
        const name = part.typeName.text;
        if (bound.has(name)) {
          if (part.typeArguments?.length)
            throw Error(`type parameter applied as constructor: ${name}`);
        } else {
          const local = localAlias(source, identity.module, name);
          const imported = local ? null :
            resolveModuleImport(identity.module, name, modules, config);
          const target = local ?? imported?.declaration;
          if (!target || target.capability === "value")
            throw Error(`unresolved type reference ${identity.module}#${name}`);
          const targetNode = alias(sourceOf(target.module), target);
          const arguments_ = part.typeArguments ?? [];
          if (arguments_.length !== (targetNode.typeParameters?.length ?? 0))
            throw Error(`type argument arity: ${target.module}#${target.name}`);
          references.push({ name, span: [part.getStart(source), part.end],
            arguments: arguments_.map(arg => [arg.getStart(source), arg.end]),
            target, route: imported?.route ?? [{ module: identity.module,
              sha256: module.sha256 }], mappings: imported?.mappings ?? [] });
          queue.push(target);
        }
      }
      part.forEachChild(child => { visit(child); });
    };
    for (const parameter of node.typeParameters ?? []) {
      if (parameter.constraint) visit(parameter.constraint);
      if (parameter.defaultType) visit(parameter.defaultType);
    }
    visit(node.type);
    definitions.push({ declaration: identity,
      sha256: module.sha256,
      parameters, body: [node.type.getStart(source), node.type.end], references });
  }
  return { root, definitions };
}
