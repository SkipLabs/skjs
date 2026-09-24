/** The declaration graph of one source file's types. TypeScript's checker,
 * under the file's configured project, decides which declaration every name
 * denotes: imports, reexports, package entries, `paths`, links and globals
 * resolve exactly as the compiler resolves them. This module turns each
 * declaration reached into a source equation, or refuses a form the fragment
 * cannot state; a refusal never drops a declaration. */
import { realpathSync } from "node:fs";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { API, DiagnosticCategory, SymbolFlags, type Checker, type Program } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, ExportDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, SourceFile, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { classInstance, members, optionalTerm, signature, typeTerm, type TermScope } from "./type-term.mts";
import type { DeclarationIdentity, DeclarationDocument, PropertyKey, Reference, TypeDefinition, TypeRoot, TypeTerm, ValueRoot } from "./declaration-types.mts";
export type { DeclarationIdentity, DeclarationDocument, Reference, TypeDefinition, TypeRoot, TypeTerm, ValueRoot } from "./declaration-types.mts";

type TypeDeclaration = TypeAliasDeclaration | InterfaceDeclaration | ClassDeclaration;
const isTypeDeclaration = (node: Node): node is TypeDeclaration =>
  ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node) || ts.isClassDeclaration(node);

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

/** The identifier at exactly `span`, in TypeScript's tree of the client. */
function identifierAt(file: SourceFile, span: Span): Identifier | null {
  const visit = (node: Node): Identifier | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (ts.isIdentifier(node) && node.getStart(file) === span[0] && node.end === span[1]) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The client's named imports: each must name exactly one declaration. */
function importBindings(client: SourceFile): { local: Identifier; imported: string;
  specifier: string; span: Span; typeOnly: boolean }[] {
  return client.statements.filter(ts.isImportDeclaration).flatMap(node => {
    const span: Span = [node.getStart(client), node.end];
    const clause = node.importClause;
    if (!clause || clause.name || !clause.namedBindings || !ts.isNamedImports(clause.namedBindings) ||
        !ts.isStringLiteral(node.moduleSpecifier))
      throw new DeclarationError(span, "only named imports are resolved");
    const specifier = node.moduleSpecifier.text;
    // The unstable AST exposes this runtime field but omits it from the
    // ImportClause interface.
    const clauseTypeOnly = "isTypeOnly" in clause && clause.isTypeOnly === true;
    return clause.namedBindings.elements.map(element => ({ local: element.name,
      imported: element.propertyName?.text ?? element.name.text, specifier, span,
      typeOnly: clauseTypeOnly || element.isTypeOnly }));
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
  /** The client's type-reference names that are neither imported nor its own
   * declarations: each that TypeScript binds to a global declaration becomes
   * a root. A type parameter is not one. */
  globals?: readonly Span[];
} = {}): DeclarationDocument {
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
      // An anonymous class is refused where it is reached, so every
      // declaration here has a name.
      return { module: idOf(source), name: node.name?.text ?? "",
        span: [node.getStart(source), node.end] };
    };
    // The one declaration TypeScript binds a name to, with no error on it or
    // on the path to it.
    const resolveDeclarations = (identifier: Identifier, what: string): Node[] => {
      const target = targetOf(checker, identifier);
      if (!target) throw Error(`unresolved type reference ${what}`);
      const nodes = target.declarations.map(d => d.resolve());
      if (nodes.some(node => !node)) throw Error(`unresolved type reference ${what}`);
      for (const statement of statementsOnPath(checker, identifier))
        clean(statement, `${idOf(statement.getSourceFile())} on the path to ${what}`);
      return nodes as Node[];
    };
    const resolveDeclaration = (identifier: Identifier, what: string): Node => {
      const nodes = resolveDeclarations(identifier, what);
      if (nodes.length !== 1)
        throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
      return nodes[0] as Node;
    };
    // An interface declared several times is one interface with every
    // declaration's members, as TypeScript merges it; the first declaration is
    // its identity. A same-named value declaration is the name's other
    // meaning, which a type reference does not denote.
    const partners = new Map<TypeDeclaration, TypeDeclaration[]>();
    const lookup = (identifier: Identifier, what: string): TypeDeclaration => {
      const nodes = resolveDeclarations(identifier, what);
      const types = nodes.filter(isTypeDeclaration);
      const [node] = types;
      if (!node || nodes.some(n => !isTypeDeclaration(n) && !ts.isVariableDeclaration(n)) ||
          (types.length > 1 && !types.every(ts.isInterfaceDeclaration)))
        throw Error(types.length > 1 || nodes.length > 1
          ? `TypeScript found ${nodes.length} declarations for ${what}`
          : `${what} is not one type alias, interface or class`);
      const names = (n: TypeDeclaration) => (n.typeParameters ?? []).map(p => p.name.text).join(",");
      for (const part of types) {
        if (!part.name) throw Error(`${what} is not one type alias, interface or class`);
        if (names(part) !== names(node))
          throw Error(`the merged declarations of ${what} have different type parameters`);
        clean(part, `${idOf(part.getSourceFile())}#${part.name.text}`);
      }
      partners.set(node, types);
      return node;
    };
    // A computed key names a `unique symbol` constant. Each such declaration
    // is listed once, and its position in the list is the symbol's identity.
    const symbols: DeclarationIdentity[] = [];
    const symbolIndex = new Map<string, number>();
    // A well-known symbol such as `Symbol.iterator` is a readonly property
    // declared `unique symbol`, and that property is its identity.
    const symbolOf = (written: Identifier | ts.PropertyAccessExpression): number => {
      const name = ts.isIdentifier(written) ? written : written.name;
      if (!ts.isIdentifier(name)) throw Error("a computed key names a symbol");
      const what = `[${ts.isIdentifier(written) ? written.text : `${written.expression.getText()}.${name.text}`}]`;
      const node = resolveDeclaration(name, what);
      const type = ts.isVariableDeclaration(node) || ts.isPropertySignatureDeclaration(node) ? node.type : undefined;
      const constant = ts.isVariableDeclaration(node) && ts.isVariableDeclarationList(node.parent) &&
        !!(node.parent.flags & ts.NodeFlags.Const);
      const property = ts.isPropertySignatureDeclaration(node) && !node.postfixToken &&
        node.modifiers?.length === 1 && node.modifiers[0]?.kind === ts.SyntaxKind.ReadonlyKeyword;
      if (!(constant || property) || !node.name || !ts.isIdentifier(node.name) ||
          !type || !ts.isTypeOperatorNode(type) || type.operator !== ts.SyntaxKind.UniqueKeyword ||
          type.type.kind !== ts.SyntaxKind.SymbolKeyword)
        throw Error(`the computed key ${what} is not a unique symbol constant`);
      const source = node.getSourceFile();
      clean(node, `${idOf(source)}#${node.name.text}`);
      const identity: DeclarationIdentity = { module: idOf(source), name: node.name.text,
        span: [node.getStart(source), node.end] };
      const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
      let index = symbolIndex.get(key);
      if (index === undefined) {
        index = symbols.length;
        symbols.push(identity);
        symbolIndex.set(key, index);
      }
      return index;
    };
    // The type an imported value's declaration states, and the declarations
    // that type reaches, which join the graph.
    const valueStarts: TypeDeclaration[] = [];
    const valueScope = (node: Node, what: string, binders: string[] = []): TermScope => {
      const source = node.getSourceFile();
      return {
        source,
        annotation: false,
        symbol: symbolOf,
        fail: (_node, message) => { throw Error(`${message} in ${what}`); },
        named: (part, pos, read) => {
          const name = part.typeName as Identifier;
          if (binders.includes(name.text)) {
            if (part.typeArguments?.length) throw Error(`type parameter applied as constructor: ${name.text}`);
            return { k: "binder", name: name.text, span: pos };
          }
          const targetNode = lookup(name, `${idOf(source)}#${name.text}`);
          const parameters = targetNode.typeParameters ?? [];
          const args = part.typeArguments ?? [];
          if (args.length < parameters.filter(p => !p.defaultType).length || args.length > parameters.length)
            throw Error(`type argument arity: ${identityOf(targetNode).module}#${name.text}`);
          valueStarts.push(targetNode);
          return { k: "reference", reference: { name: name.text, span: pos,
            arguments: args.map(arg => [arg.getStart(source), arg.end] as Span), target: identityOf(targetNode) },
            args: args.map(read), span: pos };
        },
      };
    };
    // A generic declaration's binders, each bounded by what it extends; the
    // bound may name earlier binders.
    const bindersOf = (parameters: readonly ts.TypeParameterDeclaration[] | undefined, node: Node, what: string) => {
      const names: string[] = [];
      const typeParams = (parameters ?? []).map(p => {
        if (p.defaultType) throw Error(`a type parameter default of an imported value is outside the fragment: ${what}`);
        const bound = p.constraint ? typeTerm(valueScope(node, what, [...names]), p.constraint, p) : null;
        names.push(p.name.text);
        return { name: p.name.text, bound };
      });
      return { names, typeParams };
    };
    const valueOf = (node: Node, what: string): Omit<ValueRoot, "binding"> => {
      const source = node.getSourceFile();
      const span: Span = [node.getStart(source), node.end];
      if (ts.isFunctionDeclaration(node) && node.name) {
        // Only the signature is the contract; the body is what is assumed,
        // so an error inside it is not the graph's.
        for (const part of [...(node.typeParameters ?? []), ...node.parameters, ...(node.type ? [node.type] : [])])
          clean(part, `${idOf(source)}#${node.name.text}`);
        const { names, typeParams } = bindersOf(node.typeParameters, node, what);
        return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false, typeParams,
          type: signature(valueScope(node, what, names), node.parameters, node.type, node, span, true) };
      }
      if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name)) {
        const list = node.parent;
        if (!ts.isVariableDeclarationList(list) || !(list.flags & ts.NodeFlags.Const) || !node.type)
          throw Error(`an imported value must be an annotated constant, function or class: ${what}`);
        clean(node, `${idOf(source)}#${node.name.text}`);
        return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false,
          typeParams: [], type: typeTerm(valueScope(node, what), node.type, node) };
      }
      if (ts.isClassDeclaration(node) && node.name) {
        clean(node, `${idOf(source)}#${node.name.text}`);
        const { names, typeParams } = bindersOf(node.typeParameters, node, what);
        const scope = valueScope(node, what, names);
        const constructor = node.members.find(ts.isConstructorDeclaration);
        // A defaulted parameter may be omitted: `undefined` is what a short
        // call binds there, and the default replaces it.
        const params = (constructor?.parameters ?? []).map(p => {
          if (!ts.isIdentifier(p.name) || p.dotDotDotToken)
            throw Error(`an imported class constructor needs plain parameters: ${what}`);
          const type = typeTerm(scope, p.type, p);
          return p.questionToken || p.initializer ? optionalTerm(type, [p.getStart(source), p.end]) : type;
        });
        const identity = identityOf(node);
        valueStarts.push(node);
        const nameSpan: Span = [node.name.getStart(source), node.name.end];
        return { declaration: identity, construct: true, typeParams, type: { k: "constructor", params,
          result: { k: "reference", reference: { name: node.name.text, span: nameSpan,
            arguments: names.map(() => nameSpan), target: identity },
            args: names.map(name => ({ k: "binder", name, span: nameSpan })), span: nameSpan }, span } };
      }
      throw Error(`${what} is not an annotated constant, function or class`);
    };
    const roots: { root: TypeRoot; node: TypeDeclaration }[] = [];
    const values: ValueRoot[] = [];
    for (const binding of importBindings(client)) {
      try {
        const node = resolveDeclaration(binding.local, binding.local.text);
        // A class is a type and, imported as a value, a constructor too.
        if (!binding.typeOnly && !(ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)))
          values.push({ binding: { local: binding.local.text, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...valueOf(node, binding.local.text) });
        if (!isTypeDeclaration(node)) continue;
        const declaration = lookup(binding.local, binding.local.text);
        roots.push({ node: declaration, root: { binding: { kind: "import", local: binding.local.text,
          imported: binding.imported, specifier: binding.specifier, span: binding.span },
        declaration: identityOf(declaration) } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        throw new DeclarationError(binding.span, error instanceof Error ? error.message : String(error));
      }
    }
    for (const span of options.locals ?? []) {
      const declaration = client.statements.find(statement =>
        isTypeDeclaration(statement) &&
        statement.getStart(client) === span[0] && statement.end === span[1]);
      if (!declaration || !isTypeDeclaration(declaration) || !declaration.name)
        throw new DeclarationError(span, "TypeScript local declaration missing");
      try {
        const node = lookup(declaration.name, declaration.name.text);
        // A merged interface's later declarations are the same root.
        if (roots.some(r => r.node === node)) continue;
        roots.push({ node, root: { binding: { kind: "local", local: declaration.name.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    for (const span of options.globals ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript global reference missing");
      if (roots.some(r => r.root.binding.local === identifier.text)) continue;
      const declaration = targetOf(checker, identifier)?.declarations[0]?.resolve();
      if (!declaration || ts.isTypeParameterDeclaration(declaration) ||
          declaration.getSourceFile().fileName === client.fileName) continue;
      try {
        const node = lookup(identifier, identifier.text);
        roots.push({ node, root: { binding: { kind: "global", local: identifier.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    const seen = new Set<string>();
    const definitions: TypeDefinition[] = [];
    for (const { root, node: start } of roots) {
      try {
        collect(start, seen, definitions, lookup, identityOf, symbolOf, partners);
      } catch (error) {
        throw new DeclarationError(root.binding.span,
          error instanceof Error ? error.message : String(error));
      }
    }
    for (const [index, start] of valueStarts.entries()) {
      try {
        collect(start, seen, definitions, lookup, identityOf, symbolOf, partners);
      } catch (error) {
        throw new DeclarationError(values[Math.min(index, values.length - 1)]?.binding.span ?? [0, 0],
          error instanceof Error ? error.message : String(error));
      }
    }
    return { roots: roots.map(r => r.root), definitions, values, symbols };
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

/** A merged interface's body: every part's fields, calls and at most one
 * string index, with no field named twice. The first part's span stands for
 * the whole. */
function mergeMembers(parts: TypeTerm[], fail: (at: Node, message: string) => never, at: Node): TypeTerm {
  const [first, ...rest] = parts;
  if (!first || first.k !== "object") return fail(at, "an interface body is a record");
  if (!rest.length) return first;
  const fields = [...first.fields];
  let stringIndex = first.stringIndex;
  const calls = [...first.calls];
  const key = (name: PropertyKey) => typeof name === "string" ? name : `[symbol ${name.symbol}]`;
  for (const part of rest) {
    if (part.k !== "object") return fail(at, "an interface body is a record");
    for (const field of part.fields) {
      if (fields.some(f => key(f.name) === key(field.name)))
        fail(at, "a merged interface declares a member twice");
      fields.push(field);
    }
    if (part.stringIndex) {
      if (stringIndex) fail(at, "a merged interface declares two string index signatures");
      stringIndex = part.stringIndex;
    }
    calls.push(...part.calls);
  }
  return { ...first, fields, stringIndex, calls };
}

/** Every declaration reachable from `start`, each once across roots. */
function collect(start: TypeDeclaration, seen: Set<string>, definitions: TypeDefinition[],
  lookup: (identifier: Identifier, what: string) => TypeDeclaration,
  identityOf: (node: TypeDeclaration) => DeclarationIdentity,
  symbol: (identifier: Identifier) => number,
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>): void {
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
    const reference = (source: SourceFile, identifier: Identifier, arguments_: readonly TypeNode[], pos: Span,
        read: (part: TypeNode) => TypeTerm): TypeTerm => {
      const targetNode = lookup(identifier, `${identity.module}#${identifier.text}`);
      const target = identityOf(targetNode);
      const targetParameters = targetNode.typeParameters ?? [];
      const required = targetParameters.filter(p => !p.defaultType).length;
      if (arguments_.length < required || arguments_.length > targetParameters.length)
        throw Error(`type argument arity: ${target.module}#${target.name}`);
      const edge: Reference = { name: identifier.text, span: pos,
        arguments: arguments_.map(arg => [arg.getStart(source), arg.end]), target };
      queue.push(targetNode);
      return { k: "reference", reference: edge, args: arguments_.map(read), span: pos };
    };
    // Each declaration part is read in its own file, which its spans index.
    const scopeOf = (source: SourceFile): TermScope => ({
      source,
      annotation: false,
      symbol,
      fail: (_node, message) => { throw Error(`${message} in ${identity.module}#${identity.name}`); },
      named: (part, pos, read) => {
        const name = part.typeName as Identifier;
        const index = parameterNames.indexOf(name.text);
        if (index < 0) return reference(source, name, part.typeArguments ?? [], pos, read);
        if (part.typeArguments?.length)
          throw Error(`type parameter applied as constructor: ${name.text}`);
        return { k: "parameter", index, span: pos };
      },
    });
    const scope = scopeOf(source);
    const parse = (part: TypeNode): TypeTerm => typeTerm(scope, part);
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
    const parts = partners.get(node) ?? [node];
    const expression = ts.isTypeAliasDeclaration(node)
      ? parse(node.type)
      : ts.isClassDeclaration(node)
        ? classInstance(scope, node, [node.getStart(source), node.end])
        : mergeMembers(parts.map(part => {
            const file = part.getSourceFile();
            return members(scopeOf(file), (part as ts.InterfaceDeclaration).members, part,
              [part.getStart(file), part.end], true);
          }), (at, message) => scope.fail(at, message), node);
    // A class's `implements` clauses are obligations on the class, not part of
    // its instance type; the class it extends is a base of that type, as an
    // interface's are.
    const bases = parts.flatMap(part => {
      if (!ts.isInterfaceDeclaration(part) && !ts.isClassDeclaration(part)) return [];
      const file = part.getSourceFile();
      const read = (t: TypeNode): TypeTerm => typeTerm(scopeOf(file), t);
      return (part.heritageClauses ?? []).filter(clause =>
          !(ts.isClassDeclaration(part) && clause.token === ts.SyntaxKind.ImplementsKeyword)).flatMap(clause => {
          if (clause.token !== ts.SyntaxKind.ExtendsKeyword)
            throw Error(`unsupported heritage in ${identity.module}#${identity.name}`);
          return clause.types.map(base => {
            if (!ts.isIdentifier(base.expression))
              throw Error(`qualified heritage in ${identity.module}#${identity.name}`);
            return reference(file, base.expression, base.typeArguments ?? [],
              [base.getStart(file), base.end], read);
          });
        });
    });
    definitions.push({ declaration: identity, parameters, bases, expression });
  }
}
