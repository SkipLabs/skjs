/** The declaration graph of one source file's types. TypeScript's checker,
 * under the file's configured project, decides which declaration every name
 * denotes: imports, reexports, package entries, `paths`, links and globals
 * resolve exactly as the compiler resolves them. This module turns each
 * declaration reached into a source equation, or refuses a form the fragment
 * cannot state; a refusal never drops a declaration. */
import { createHash } from "node:crypto";
import { realpathSync } from "node:fs";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { API, DiagnosticCategory, SymbolFlags, type Checker, type Program } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ExportDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, SourceFile, TypeAliasDeclaration, TypeElement, TypeNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { DeclarationIdentity, ImportDocument, Reference, TypeDefinition, TypeRoot, TypeTerm } from "./imported-types.mts";
export type { DeclarationIdentity, ImportDocument, Reference, TypeDefinition, TypeRoot, TypeTerm } from "./imported-types.mts";

type TypeDeclaration = TypeAliasDeclaration | InterfaceDeclaration;

/** A refusal located at a root of the client: an import declaration or one of
 * its own type declarations. */
export class DeclarationError extends Error {
  readonly at: Span;
  constructor(at: Span, message: string) {
    super(message);
    this.at = at;
  }
}

/** The configured project named on a command line: a tsconfig file, or the
 * directory holding one. */
export function tsconfigOf(path: string): string {
  const absolute = resolve(path);
  return absolute.endsWith(".json") ? absolute : join(absolute, "tsconfig.json");
}

const digest = (text: string): string => createHash("sha256").update(text).digest("hex");

/** Open `file` in its configured TypeScript project, which must be strict:
 * `tsconfigPath` when given, otherwise the project that owns the file. The
 * compiler reads the files on disk; nothing here overrides their text. */
function withProject<T>(file: string, tsconfigPath: string | undefined,
  use: (checker: Checker, client: SourceFile, root: string, program: Program) => T): T {
  const api = new API({ cwd: dirname(file) });
  try {
    const snapshot = api.updateSnapshot({ openFiles: [file],
      ...(tsconfigPath ? { openProjects: [tsconfigPath] } : {}) });
    const project = tsconfigPath
      ? snapshot.getProject(tsconfigPath)
      : snapshot.getDefaultProjectForFile(file);
    if (!project?.configFileName || !project.compilerOptions.strict)
      throw new DeclarationError([0, 0], `TypeScript did not load a strict tsconfig for ${file}`);
    const client = project.program.getSourceFile(file);
    if (!client) throw new DeclarationError([0, 0], `TypeScript did not load ${file}`);
    return use(project.checker, client, dirname(project.configFileName), project.program);
  } finally {
    api.close();
  }
}

/** A module's identity: the client by its absolute path, a standard library
 * file by name, anything else by its real path relative to the project. */
function moduleIds(clientFile: string, root: string): (file: SourceFile) => string {
  const client = realpathSync(clientFile);
  const projectRoot = realpathSync(root);
  return file => {
    const path = realpathSync(file.fileName);
    if (path === client) return clientFile;
    const inside = relative(projectRoot, path).split(sep).join("/");
    if (/^lib\..*\.d\.ts$/.test(basename(path)) && inside.startsWith("../"))
      return `typescript/lib/${basename(path)}`;
    return inside;
  };
}

/** What TypeScript binds `identifier` to, following import and export aliases. */
function targetOf(checker: Checker, identifier: Identifier) {
  const symbol = checker.getSymbolAtLocation(identifier);
  if (!symbol) return null;
  // getAliasedSymbol requires an alias: calling it on a symbol that already
  // denotes its declaration panics in tsgo.
  const target = symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
  // An unbound name yields either the unknown symbol or one with no declaration.
  return checker.isUnknownSymbol(target) || target.declarations.length === 0 ? null : target;
}

/** The import and export statements TypeScript passes through when it binds
 * `identifier`: each step of its alias chain, and, because an `export *` is
 * not an alias step, every star export of each module those statements name. */
function statementsOnPath(checker: Checker, identifier: Identifier):
  (ImportDeclaration | ExportDeclaration)[] {
  const out: (ImportDeclaration | ExportDeclaration)[] = [];
  const modules = new Set<string>();
  const starExports = (specifier: Node): void => {
    const module = checker.getSymbolAtLocation(specifier)?.declarations[0]?.resolve();
    if (!module || !ts.isSourceFile(module) || modules.has(module.fileName)) return;
    modules.add(module.fileName);
    for (const statement of module.statements)
      if (ts.isExportDeclaration(statement) && statement.moduleSpecifier && !statement.exportClause) {
        out.push(statement);
        starExports(statement.moduleSpecifier);
      }
  };
  let symbol = checker.getSymbolAtLocation(identifier);
  const seen = new Set<number>();
  while (symbol && symbol.flags & SymbolFlags.Alias && !seen.has(symbol.id)) {
    seen.add(symbol.id);
    let node: Node | undefined = symbol.declarations[0]?.resolve();
    while (node && !ts.isImportDeclaration(node) && !ts.isExportDeclaration(node) && !ts.isSourceFile(node))
      node = node.parent;
    if (node && (ts.isImportDeclaration(node) || ts.isExportDeclaration(node))) {
      out.push(node);
      if (node.moduleSpecifier) starExports(node.moduleSpecifier);
    }
    symbol = checker.getImmediateAliasedSymbol(symbol);
  }
  return out;
}

/** The client's named imports: each must name exactly one declaration. */
function importBindings(client: SourceFile): { local: Identifier; imported: string;
  specifier: string; span: Span }[] {
  return client.statements.filter(ts.isImportDeclaration).flatMap(node => {
    const span: Span = [node.getStart(client), node.end];
    const clause = node.importClause;
    if (!clause || clause.name || !clause.namedBindings || !ts.isNamedImports(clause.namedBindings) ||
        !ts.isStringLiteral(node.moduleSpecifier))
      throw new DeclarationError(span, "only named imports are resolved");
    const specifier = node.moduleSpecifier.text;
    return clause.namedBindings.elements.map(element => ({ local: element.name,
      imported: element.propertyName?.text ?? element.name.text, specifier, span }));
  });
}

/**
 * The declaration graph of `file`: one root per named import and per local
 * declaration at a span in `locals`, and every declaration reachable from them.
 * `client`, when given, is the parser's tree of the same file; TypeScript must
 * have read the same bytes, so the spans of both trees agree.
 */
export function collectDeclarations(file: string, options: {
  tsconfigPath?: string;
  client?: SourceFile;
  locals?: readonly Span[];
} = {}): ImportDocument {
  const clientFile = resolve(file);
  return withProject(clientFile, options.tsconfigPath, (checker, client, root, program) => {
    if (options.client && options.client.getFullText() !== client.getFullText())
      throw new DeclarationError([0, 0], "TypeScript client source bytes differ");
    const idOf = moduleIds(clientFile, root);
    // Everything the graph uses must be code TypeScript accepts: an error in a
    // used declaration or on the resolution path refuses it. Errors elsewhere in
    // those files, and in the client's function bodies, are not the graph's.
    const errors = new Map<string, readonly { pos: number; end: number; text: string }[]>();
    const clean = (node: Node, what: string): void => {
      const file = node.getSourceFile();
      let found = errors.get(file.fileName);
      if (!found) {
        found = [...program.getSyntacticDiagnostics(file.fileName),
          ...program.getSemanticDiagnostics(file.fileName)]
          .filter(d => d.category === DiagnosticCategory.Error);
        errors.set(file.fileName, found);
      }
      const start = node.getStart(file);
      const error = found.find(d => d.pos < node.end && d.end > start);
      if (error) throw Error(`TypeScript reports an error in ${what}: ${error.text}`);
    };
    const identityOf = (node: TypeDeclaration): DeclarationIdentity => {
      const source = node.getSourceFile();
      return { module: idOf(source), name: node.name.text,
        span: [node.getStart(source), node.end] };
    };
    const lookup = (identifier: Identifier, what: string): TypeDeclaration => {
      const target = targetOf(checker, identifier);
      if (!target) throw Error(`unresolved type reference ${what}`);
      if (target.declarations.length !== 1)
        throw Error(`TypeScript found ${target.declarations.length} declarations for ${what}`);
      const node = target.declarations[0]?.resolve();
      if (!node || !(ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)))
        throw Error(`${what} is not one type alias or interface`);
      for (const statement of statementsOnPath(checker, identifier))
        clean(statement, `${idOf(statement.getSourceFile())} on the path to ${what}`);
      clean(node, `${idOf(node.getSourceFile())}#${node.name.text}`);
      return node;
    };
    const roots: { root: TypeRoot; node: TypeDeclaration }[] = [];
    for (const binding of importBindings(client)) {
      try {
        const node = lookup(binding.local, binding.local.text);
        roots.push({ node, root: { binding: { kind: "import", local: binding.local.text,
          imported: binding.imported, specifier: binding.specifier, span: binding.span },
        declaration: identityOf(node) } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        throw new DeclarationError(binding.span, error instanceof Error ? error.message : String(error));
      }
    }
    for (const span of options.locals ?? []) {
      const declaration = client.statements.find(statement =>
        (ts.isTypeAliasDeclaration(statement) || ts.isInterfaceDeclaration(statement)) &&
        statement.getStart(client) === span[0] && statement.end === span[1]);
      if (!declaration || !(ts.isTypeAliasDeclaration(declaration) || ts.isInterfaceDeclaration(declaration)))
        throw new DeclarationError(span, "TypeScript local declaration missing");
      try {
        const node = lookup(declaration.name, declaration.name.text);
        roots.push({ node, root: { binding: { kind: "local", local: declaration.name.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    const seen = new Set<string>();
    const definitions: TypeDefinition[] = [];
    for (const { root, node: start } of roots) {
      try {
        collect(start, seen, definitions, lookup, identityOf);
      } catch (error) {
        throw new DeclarationError(root.binding.span,
          error instanceof Error ? error.message : String(error));
      }
    }
    return { roots: roots.map(r => r.root), definitions };
  });
}

/** Where each named import of `file` resolves, whatever kind of declaration
 * it is. Provenance for declarations the fragment cannot yet interpret; never
 * a typing certificate. */
export function importTargets(file: string, tsconfigPath?: string):
  { local: string; module: string; name: string; span: Span; kind: string }[] {
  const clientFile = resolve(file);
  return withProject(clientFile, tsconfigPath, (checker, client, root) => {
    const idOf = moduleIds(clientFile, root);
    return importBindings(client).map(binding => {
      const target = targetOf(checker, binding.local);
      if (!target || target.declarations.length !== 1)
        throw new DeclarationError(binding.span, `no single declaration for ${binding.local.text}`);
      const node = target.declarations[0]?.resolve();
      if (!node) throw new DeclarationError(binding.span, `no declaration for ${binding.local.text}`);
      const source = node.getSourceFile();
      return { local: binding.local.text, module: idOf(source), name: target.name,
        span: [node.getStart(source), node.end], kind: ts.SyntaxKind[node.kind] ?? "unknown" };
    });
  });
}

/** Every declaration reachable from `start`, each once across roots. */
function collect(start: TypeDeclaration, seen: Set<string>, definitions: TypeDefinition[],
  lookup: (identifier: Identifier, what: string) => TypeDeclaration,
  identityOf: (node: TypeDeclaration) => DeclarationIdentity): void {
  const queue: TypeDeclaration[] = [start];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const node = queue[cursor];
    if (!node) throw Error("missing queued declaration");
    const identity = identityOf(node);
    const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const source = node.getSourceFile();
    const parameterNodes = node.typeParameters ?? [];
    const parameterNames = parameterNodes.map(parameter => parameter.name.text);
    if (new Set(parameterNames).size !== parameterNames.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
    const references: Reference[] = [];
    const span = (part: TypeNode): Span => [part.getStart(source), part.end];
    const reference = (identifier: Identifier, arguments_: readonly TypeNode[], pos: Span): TypeTerm => {
      const targetNode = lookup(identifier, `${identity.module}#${identifier.text}`);
      const target = identityOf(targetNode);
      const targetParameters = targetNode.typeParameters ?? [];
      const required = targetParameters.filter(p => !p.defaultType).length;
      if (arguments_.length < required || arguments_.length > targetParameters.length)
        throw Error(`type argument arity: ${target.module}#${target.name}`);
      const edge: Reference = { name: identifier.text, span: pos,
        arguments: arguments_.map(arg => [arg.getStart(source), arg.end]), target };
      references.push(edge);
      queue.push(targetNode);
      return { k: "reference", reference: edge, args: arguments_.map(parse), span: pos };
    };
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
        const { params, rest } = parseParameters(parameters, "function");
        return { k: "function", receiver, params, rest, result: parse(part.type), span: pos };
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
        return reference(part.typeName, part.typeArguments ?? [], pos);
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
    const parseParameters = (parameters: readonly ts.ParameterDeclaration[], kind: string) => {
      const params: TypeTerm[] = [];
      let rest: TypeTerm | null = null;
      let optional = false;
      for (const [index, parameter] of parameters.entries()) {
        if (!ts.isIdentifier(parameter.name) || !parameter.type || parameter.initializer ||
            parameter.name.text === "this")
          throw Error(`unsupported ${kind} parameter in ${identity.module}#${identity.name}`);
        if (parameter.dotDotDotToken) {
          if (rest || index !== parameters.length - 1 || parameter.questionToken ||
              !ts.isArrayTypeNode(parameter.type))
            throw Error(`unsupported ${kind} rest parameter in ${identity.module}#${identity.name}`);
          rest = parse(parameter.type.elementType);
        } else {
          if (optional && !parameter.questionToken)
            throw Error(`required ${kind} parameter after optional in ${identity.module}#${identity.name}`);
          const type = parse(parameter.type);
          if (parameter.questionToken) {
            optional = true;
            params.push({ k: "union", parts: [type,
              { k: "atom", name: "undefined", span: [parameter.getStart(source), parameter.end] }],
              span: [parameter.getStart(source), parameter.end] });
          } else params.push(type);
        }
      }
      return { params, rest };
    };
    const parseMembers = (members: readonly TypeElement[], pos: Span,
      allowMethods: boolean): TypeTerm => {
      const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
      let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
      const calls: Extract<TypeTerm, { k: "function" }>[] = [];
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
          const { params, rest } = parseParameters(member.parameters, "method");
          const methodSpan: Span = [member.getStart(source), member.end];
          fields.push({ name, optional: false, readonly: false,
            type: { k: "function", receiver: { k: "self", span: methodSpan },
              params, rest, result: parse(member.type), span: methodSpan },
            span: methodSpan });
        } else if (ts.isIndexSignatureDeclaration(member)) {
          if (stringIndex || member.parameters.length !== 1 ||
              member.parameters[0]?.type?.kind !== ts.SyntaxKind.StringKeyword || !member.type ||
              member.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword))
            throw Error(`unsupported index signature in ${identity.module}#${identity.name}`);
          stringIndex = { readonly: member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
            value: parse(member.type), span: [member.getStart(source), member.end] };
        } else if (ts.isCallSignatureDeclaration(member)) {
          if (member.typeParameters?.length || !member.type)
            throw Error(`generic or incomplete call signature in ${identity.module}#${identity.name}`);
          const head = member.parameters[0];
          const hasReceiver = !!head && ts.isIdentifier(head.name) && head.name.text === "this";
          let receiver: TypeTerm | null = null;
          if (hasReceiver) {
            if (!head?.type || head.questionToken || head.dotDotDotToken || head.initializer)
              throw Error(`unsupported call receiver in ${identity.module}#${identity.name}`);
            receiver = parse(head.type);
          }
          const { params, rest } = parseParameters(hasReceiver ? member.parameters.slice(1) : member.parameters,
            "call signature");
          calls.push({ k: "function", receiver, params, rest, result: parse(member.type),
            span: [member.getStart(source), member.end] });
        } else throw Error(`unsupported object member in ${identity.module}#${identity.name}`);
      }
      return { k: "object", fields, stringIndex, calls, span: pos };
    };
    let sawDefault = false;
    const parameters = parameterNodes.map(parameter => {
      if (sawDefault && !parameter.defaultType)
        throw Error(`required type parameter after default in ${identity.module}#${identity.name}`);
      sawDefault ||= !!parameter.defaultType;
      const parameterSpan: Span = [parameter.getStart(source), parameter.end];
      return { name: parameter.name.text, span: parameterSpan,
        bound: parameter.constraint ? parse(parameter.constraint) : null,
        default: parameter.defaultType ? parse(parameter.defaultType) : null };
    });
    const expression = ts.isTypeAliasDeclaration(node)
      ? parse(node.type)
      : parseMembers(node.members, [node.getStart(source), node.end], true);
    const bases = ts.isInterfaceDeclaration(node)
      ? (node.heritageClauses ?? []).flatMap(clause => {
          if (clause.token !== ts.SyntaxKind.ExtendsKeyword)
            throw Error(`unsupported heritage in ${identity.module}#${identity.name}`);
          return clause.types.map(base => {
            if (!ts.isIdentifier(base.expression))
              throw Error(`qualified heritage in ${identity.module}#${identity.name}`);
            return reference(base.expression, base.typeArguments ?? [],
              [base.getStart(source), base.end]);
          });
        })
      : [];
    definitions.push({ declaration: identity,
      sha256: digest(source.getFullText()),
      parameters, body: ts.isTypeAliasDeclaration(node)
        ? [node.type.getStart(source), node.type.end]
        : [node.getStart(source), node.end], bases, expression, references });
  }
}
