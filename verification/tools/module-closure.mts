/** The reachable *source declaration* closure of an imported type. This is a
 * finite provenance graph, not yet an interpretation of those declarations as
 * semantic types. Unsupported binding forms fail instead of disappearing. */
import { createHash } from "node:crypto";
import * as ts from "typescript/unstable/ast";
import type { SourceFile, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";
import { resolveModuleImport, type DeclarationIdentity,
  type ModuleSource, type ResolutionConfig, type ResolvedImport } from "./module-resolve.mts";
import type { Span } from "./span.mts";
import type { Reference, TypeClosure, TypeDefinition, TypeTerm } from "./imported-types.mts";
export type { Reference, TypeClosure, TypeDefinition, TypeTerm } from "./imported-types.mts";

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
    const parameterNodes = node.typeParameters ?? [];
    const parameterNames = parameterNodes.map(parameter => parameter.name.text);
    if (new Set(parameterNames).size !== parameterNames.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
    const references: Reference[] = [];
    const span = (part: TypeNode): Span => [part.getStart(source), part.end];
    const parse = (part: TypeNode): TypeTerm => {
      const pos = span(part);
      const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm =>
        ({ k: "atom", name, span: pos });
      switch (part.kind) {
        case ts.SyntaxKind.NullKeyword: return atom("null");
        case ts.SyntaxKind.UndefinedKeyword: return atom("undefined");
        case ts.SyntaxKind.BooleanKeyword: return atom("boolean");
        case ts.SyntaxKind.NumberKeyword: return atom("number");
        case ts.SyntaxKind.StringKeyword: return atom("string");
        case ts.SyntaxKind.UnknownKeyword: return atom("unknown");
        case ts.SyntaxKind.NeverKeyword: return atom("never");
        case ts.SyntaxKind.VoidKeyword: return atom("void");
      }
      if (ts.isParenthesizedTypeNode(part)) return parse(part.type);
      if (ts.isUnionTypeNode(part) || ts.isIntersectionTypeNode(part))
        return { k: ts.isUnionTypeNode(part) ? "union" : "intersection",
          parts: part.types.map(parse), span: pos };
      if (ts.isArrayTypeNode(part))
        return { k: "array", readonly: false, element: parse(part.elementType), span: pos };
      if (ts.isTypeOperatorNode(part) && part.operator === ts.SyntaxKind.ReadonlyKeyword &&
          ts.isArrayTypeNode(part.type))
        return { k: "array", readonly: true, element: parse(part.type.elementType), span: pos };
      if (ts.isLiteralTypeNode(part)) {
        const literal = part.literal;
        if (literal.kind === ts.SyntaxKind.NullKeyword) return atom("null");
        if (literal.kind === ts.SyntaxKind.TrueKeyword || literal.kind === ts.SyntaxKind.FalseKeyword)
          return { k: "literal", name: literal.kind === ts.SyntaxKind.TrueKeyword ? "true" : "false",
            text: literal.getText(source), span: pos };
        if (ts.isStringLiteral(literal) || ts.isNumericLiteral(literal))
          return { k: "literal", name: ts.isStringLiteral(literal) ? "string" : "number",
            text: literal.getText(source), span: pos };
      }
      if (ts.isTypeLiteralNode(part)) {
        const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
        let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
        const names = new Set<string>();
        for (const member of part.members) {
          if (ts.isPropertySignatureDeclaration(member)) {
            if (!member.name || !member.type ||
                !(ts.isIdentifier(member.name) || ts.isStringLiteral(member.name)) ||
                member.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword))
              throw Error(`unsupported property signature in ${identity.module}#${identity.name}`);
            const name = member.name.text;
            if (names.has(name)) throw Error(`duplicate named field ${identity.module}#${name}`);
            names.add(name);
            fields.push({ name, optional: member.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
              readonly: member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
              type: parse(member.type), span: [member.getStart(source), member.end] });
          } else if (ts.isIndexSignatureDeclaration(member)) {
            if (stringIndex || member.parameters.length !== 1 ||
                member.parameters[0]?.type?.kind !== ts.SyntaxKind.StringKeyword || !member.type ||
                member.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword))
              throw Error(`unsupported index signature in ${identity.module}#${identity.name}`);
            stringIndex = { readonly: member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
              value: parse(member.type), span: [member.getStart(source), member.end] };
          } else throw Error(`unsupported object member in ${identity.module}#${identity.name}`);
        }
        return { k: "object", fields, stringIndex, span: pos };
      }
      if (ts.isTypeReferenceNode(part)) {
        if (!ts.isIdentifier(part.typeName))
          throw Error(`qualified type reference in ${identity.module}#${identity.name}`);
        const name = part.typeName.text;
        const index = parameterNames.indexOf(name);
        if (index >= 0) {
          if (part.typeArguments?.length)
            throw Error(`type parameter applied as constructor: ${name}`);
          return { k: "parameter", index, span: pos };
        }
        const local = localAlias(source, identity.module, name);
        const imported = local ? null : resolveModuleImport(identity.module, name, modules, config);
        const target = local ?? imported?.declaration;
        if (!target || target.capability === "value")
          throw Error(`unresolved type reference ${identity.module}#${name}`);
        const targetNode = alias(sourceOf(target.module), target);
        const arguments_ = part.typeArguments ?? [];
        if (arguments_.length !== (targetNode.typeParameters?.length ?? 0))
          throw Error(`type argument arity: ${target.module}#${target.name}`);
        const reference: Reference = { name, span: pos,
          arguments: arguments_.map(arg => [arg.getStart(source), arg.end]),
          target, route: imported?.route ?? [{ module: identity.module,
            sha256: module.sha256 }], mappings: imported?.mappings ?? [] };
        references.push(reference);
        queue.push(target);
        return { k: "reference", reference, args: arguments_.map(parse), span: pos };
      }
      throw Error(`unsupported type syntax ${ts.SyntaxKind[part.kind]} in ` +
        `${identity.module}#${identity.name} at [${pos[0]},${pos[1]})`);
    };
    const parameters = parameterNodes.map(parameter => {
      if (parameter.defaultType)
        throw Error(`type parameter default in ${identity.module}#${identity.name} is not collected`);
      const parameterSpan: Span = [parameter.getStart(source), parameter.end];
      return { name: parameter.name.text, span: parameterSpan,
        bound: parameter.constraint ? parse(parameter.constraint) : null };
    });
    const expression = parse(node.type);
    definitions.push({ declaration: identity,
      sha256: module.sha256,
      parameters, body: [node.type.getStart(source), node.type.end], expression, references });
  }
  return { root, definitions };
}
