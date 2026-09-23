/** The reachable *source declaration* closure of an imported type. This is a
 * finite provenance graph, not yet an interpretation of those declarations as
 * semantic types. Single interfaces with supported members share the same
 * source equation path as aliases; unsupported forms fail instead of disappearing. */
import { createHash } from "node:crypto";
import * as ts from "typescript/unstable/ast";
import type { InterfaceDeclaration, SourceFile, TypeAliasDeclaration, TypeElement, TypeNode } from "typescript/unstable/ast";
import { resolveGlobalType, resolveModuleImport, type DeclarationIdentity,
  type ModuleSource, type ResolutionConfig, type ResolvedImport } from "./module-resolve.mts";
import type { Span } from "./span.mts";
import type { ImportDocument, Reference, TypeClosure, TypeDefinition, TypeTerm } from "./imported-types.mts";
export type { Reference, TypeClosure, TypeDefinition, TypeTerm } from "./imported-types.mts";

type TypeDeclaration = TypeAliasDeclaration | InterfaceDeclaration;

function typeDeclaration(source: SourceFile, identity: DeclarationIdentity): TypeDeclaration {
  const matches = source.statements.filter(statement =>
    (ts.isTypeAliasDeclaration(statement) || ts.isInterfaceDeclaration(statement)) &&
    statement.name.text === identity.name &&
    statement.getStart(source) === identity.span[0] && statement.end === identity.span[1]);
  if (matches.length !== 1 ||
      !(ts.isTypeAliasDeclaration(matches[0]) || ts.isInterfaceDeclaration(matches[0])))
    throw Error(`type declaration identity not found: ${identity.module}#${identity.name}`);
  return matches[0];
}

function localTypeDeclaration(source: SourceFile, moduleId: string, name: string):
  DeclarationIdentity | null {
  const matches = source.statements.filter(statement =>
    (ts.isTypeAliasDeclaration(statement) || ts.isInterfaceDeclaration(statement)) &&
    statement.name.text === name);
  if (matches.length > 1) throw Error(`ambiguous local type ${moduleId}#${name}`);
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
    const node = typeDeclaration(source, identity);
    if (ts.isInterfaceDeclaration(node) && node.heritageClauses?.length)
      throw Error(`interface inheritance in ${identity.module}#${identity.name} is not collected`);
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
      if (ts.isTupleTypeNode(part)) return parseTuple(part, false, pos);
      if (ts.isTypeOperatorNode(part) && part.operator === ts.SyntaxKind.ReadonlyKeyword &&
          ts.isArrayTypeNode(part.type))
        return { k: "array", readonly: true, element: parse(part.type.elementType), span: pos };
      if (ts.isTypeOperatorNode(part) && part.operator === ts.SyntaxKind.ReadonlyKeyword &&
          ts.isTupleTypeNode(part.type)) return parseTuple(part.type, true, pos);
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
        return parseMembers(part.members, pos, false);
      }
      if (ts.isFunctionTypeNode(part)) {
        if (part.typeParameters?.length)
          throw Error(`generic function type in ${identity.module}#${identity.name} is not collected`);
        if (!part.type)
          throw Error(`function result type in ${identity.module}#${identity.name} is missing`);
        const head = part.parameters[0];
        const hasReceiver = !!head && ts.isIdentifier(head.name) && head.name.text === "this";
        const parameters = hasReceiver ? part.parameters.slice(1) : part.parameters;
        let receiver: TypeTerm | null = null;
        if (hasReceiver) {
          if (!head?.type || head.questionToken || head.dotDotDotToken)
            throw Error(`unsupported function receiver in ${identity.module}#${identity.name}`);
          receiver = parse(head.type);
        }
        const params = parameters.map(p => {
          if (!ts.isIdentifier(p.name) || !p.type || p.questionToken ||
              p.dotDotDotToken || p.initializer || p.name.text === "this")
            throw Error(`unsupported function parameter in ${identity.module}#${identity.name}`);
          return parse(p.type);
        });
        return { k: "function", receiver, params, result: parse(part.type), span: pos };
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
        const local = localTypeDeclaration(source, identity.module, name);
        const imported = local ? null : resolveModuleImport(identity.module, name, modules, config);
        const global = local || imported ? null : resolveGlobalType(name, modules, config);
        const target = local ?? imported?.declaration ?? global?.declaration;
        if (!target || target.capability === "value")
          throw Error(`unresolved type reference ${identity.module}#${name}`);
        const targetNode = typeDeclaration(sourceOf(target.module), target);
        const arguments_ = part.typeArguments ?? [];
        if (arguments_.length !== (targetNode.typeParameters?.length ?? 0))
          throw Error(`type argument arity: ${target.module}#${target.name}`);
        const reference: Reference = { name, span: pos,
          arguments: arguments_.map(arg => [arg.getStart(source), arg.end]),
          target, route: imported?.route ?? global?.route ?? [{ module: identity.module,
            sha256: module.sha256 }], mappings: imported?.mappings ?? [] };
        references.push(reference);
        queue.push(target);
        return { k: "reference", reference, args: arguments_.map(parse), span: pos };
      }
      throw Error(`unsupported type syntax ${ts.SyntaxKind[part.kind]} in ` +
        `${identity.module}#${identity.name} at [${pos[0]},${pos[1]})`);
    };
    const parseTuple = (part: ts.TupleTypeNode, readonly: boolean, pos: Span): TypeTerm => {
      const required: TypeTerm[] = [], optional: TypeTerm[] = [];
      let rest: TypeTerm | null = null;
      for (const element of part.elements) {
        if (ts.isNamedTupleMember(element))
          throw Error(`named tuple position in ${identity.module}#${identity.name} is not collected`);
        if (ts.isRestTypeNode(element)) {
          if (rest || !ts.isArrayTypeNode(element.type))
            throw Error(`tuple rest in ${identity.module}#${identity.name} needs a final array element`);
          rest = parse(element.type.elementType);
        } else if (ts.isOptionalTypeNode(element)) {
          if (rest) throw Error(`tuple optional after rest in ${identity.module}#${identity.name}`);
          optional.push(parse(element.type));
        } else {
          if (optional.length || rest)
            throw Error(`tuple required after optional or rest in ${identity.module}#${identity.name}`);
          required.push(parse(element));
        }
      }
      return { k: "tuple", readonly, required, optional, rest, span: pos };
    };
    const parseMembers = (members: readonly TypeElement[], pos: Span,
      allowMethods: boolean): TypeTerm => {
      const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
      let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
      const names = new Set<string>();
      for (const member of members) {
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
        } else if (ts.isMethodSignatureDeclaration(member)) {
          if (!allowMethods || !member.name || !member.type ||
              !(ts.isIdentifier(member.name) || ts.isStringLiteral(member.name)) ||
              member.postfixToken?.kind === ts.SyntaxKind.QuestionToken ||
              member.typeParameters?.length || member.modifiers?.length)
            throw Error(`unsupported method signature in ${identity.module}#${identity.name}`);
          const name = member.name.text;
          if (names.has(name)) throw Error(`duplicate named field ${identity.module}#${name}`);
          names.add(name);
          const params = member.parameters.map(p => {
            if (!ts.isIdentifier(p.name) || !p.type || p.questionToken ||
                p.dotDotDotToken || p.initializer || p.name.text === "this")
              throw Error(`unsupported method parameter in ${identity.module}#${identity.name}`);
            return parse(p.type);
          });
          const methodSpan: Span = [member.getStart(source), member.end];
          fields.push({ name, optional: false, readonly: false,
            type: { k: "function", receiver: { k: "self", span: methodSpan },
              params, result: parse(member.type), span: methodSpan },
            span: methodSpan });
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
    };
    const parameters = parameterNodes.map(parameter => {
      if (parameter.defaultType)
        throw Error(`type parameter default in ${identity.module}#${identity.name} is not collected`);
      const parameterSpan: Span = [parameter.getStart(source), parameter.end];
      return { name: parameter.name.text, span: parameterSpan,
        bound: parameter.constraint ? parse(parameter.constraint) : null };
    });
    const expression = ts.isTypeAliasDeclaration(node)
      ? parse(node.type)
      : parseMembers(node.members, [node.getStart(source), node.end], true);
    definitions.push({ declaration: identity,
      sha256: module.sha256,
      parameters, body: ts.isTypeAliasDeclaration(node)
        ? [node.type.getStart(source), node.type.end]
        : [node.getStart(source), node.end], expression, references });
  }
  return { root, definitions };
}

/** Assemble every imported type definition into one document. The closure collector
 * supplies the only traversal; this step deduplicates reachable modules and
 * mapping witnesses. Hashes in the document record provenance; Lean does not
 * validate them. The source parser compares the TypeScript project's actual
 * module bytes with these source texts before accepting the document. */
export function collectImportDocument(
  roots: readonly ResolvedImport[],
  modules: readonly ModuleSource[],
  config: ResolutionConfig,
): ImportDocument {
  const definitions: TypeDefinition[] = [];
  const seen = new Set<string>();
  const moduleIds = new Set<string>();
  const mappingIds = new Set<string>();
  const includeRoute = (route: ResolvedImport["route"], mappings: ResolvedImport["mappings"]) => {
    for (const step of route) moduleIds.add(step.module);
    for (const mapping of mappings) mappingIds.add(mapping.source);
  };
  for (const root of roots) {
    includeRoute(root.route, root.mappings);
    for (const definition of collectTypeClosure(root, modules, config).definitions) {
      const key = `${definition.declaration.module}#${definition.declaration.span.join(":")}`;
      if (seen.has(key)) continue;
      seen.add(key);
      moduleIds.add(definition.declaration.module);
      for (const reference of definition.references)
        includeRoute(reference.route, reference.mappings);
      definitions.push(definition);
    }
  }
  const universe = new Map(modules.map(module => [module.id, module]));
  const sources = [...moduleIds].sort().map(id => {
    const module = universe.get(id);
    if (!module) throw Error(`module not supplied: ${id}`);
    const text = module.source.getFullText();
    return { module: id, sha256: module.sha256, text };
  });
  const mappings = [...mappingIds].sort().map(id => {
    const text = config.mappingSources.get(id);
    if (text === undefined) throw Error(`mapping source not supplied: ${id}`);
    const sha256 = createHash("sha256").update(text).digest("hex");
    return { source: id, sha256, text };
  });
  const sourceById = new Map(sources.map(source => [source.module, source]));
  const mappingById = new Map(mappings.map(mapping => [mapping.source, mapping]));
  const checkRoute = (route: ResolvedImport["route"], steps: ResolvedImport["mappings"]) => {
    for (const step of route)
      if (sourceById.get(step.module)?.sha256 !== step.sha256)
        throw Error(`route fingerprint differs: ${step.module}`);
    for (const step of steps) {
      const actual = config.links.get(step.virtual);
      if (!actual || actual.canonical !== step.canonical || actual.source !== step.source ||
          actual.sha256 !== step.sha256 || mappingById.get(step.source)?.sha256 !== step.sha256)
        throw Error(`mapping route differs: ${step.virtual}`);
    }
  };
  for (const root of roots) checkRoute(root.route, root.mappings);
  for (const definition of definitions) {
    if (sourceById.get(definition.declaration.module)?.sha256 !== definition.sha256)
      throw Error(`definition fingerprint differs: ${definition.declaration.module}`);
    for (const reference of definition.references)
      checkRoute(reference.route, reference.mappings);
  }
  return { roots: [...roots], definitions, sources, mappings };
}
