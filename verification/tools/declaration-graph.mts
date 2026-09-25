/** The declaration graph of one source file's types. TypeScript's checker,
 * under the file's configured project, decides which declaration every name
 * denotes: imports, reexports, package entries, `paths`, links and globals
 * resolve exactly as the compiler resolves them. This module turns each
 * declaration reached into a source equation, or refuses a form the fragment
 * cannot state; a refusal never drops a declaration. */
import { realpathSync } from "node:fs";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { API, DiagnosticCategory, SymbolFlags, TypeFlags, isUnionType, type Checker, type Program, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, ExportDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, SourceFile, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { classInstance, expandMapped, mapped, members, oneTerm, optionalTerm, signature, signatures, substitute, typeTerm,
  type Mapped, type TermScope } from "./type-term.mts";
import { arrayPrototype, interfaceOverlay, overlay, primitiveKinds, primitivePrototype, primitivePrototypeName, type OverlayEntry,
  type OverlayLibrary, type PrimitiveKind } from "./array-prototype.mts";
import { intrinsics, intrinsicModule } from "./intrinsics.mts";
import { globalEntry, globalsOverlay, type GlobalEntry, type Stated } from "./library-globals.mts";
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

/** A TypeScript error as the gate read it: the file TypeScript names, whether
 * that is the client, and the span, as offsets and as 0-based line and
 * character. The text is TypeScript's own. */
export interface SeenDiagnostic {
  file: string;
  client: boolean;
  pos: Span;
  start: { line: number; character: number };
  end: { line: number; character: number };
  text: string;
}

/** A standard library type whose declaration is not what it means to
 * TypeScript, so a reference to it is read as that meaning (DESIGN.md,
 * "Library types"): `Array<T>` and `ReadonlyArray<T>` are the array types
 * `T[]` and `readonly T[]`, and a library type alias whose equation is a
 * mapped type, such as `Record<K, V>`, is that mapped type at the
 * reference's arguments. */
export type LibraryType =
  | { k: "array"; readonly: boolean }
  | { k: "mapped"; parameters: number; template: Mapped };

/** A reference to `library` at `args`, located at `span`. */
export function libraryTerm(library: LibraryType, args: readonly TypeTerm[], span: Span,
    fail: (message: string) => never): TypeTerm {
  if (library.k === "array") {
    const [element] = args;
    if (!element || args.length !== 1) return fail("an array type takes one type argument");
    return { k: "array", readonly: library.readonly, element, span };
  }
  if (args.length !== library.parameters) return fail("a mapped library type needs all its type arguments");
  const t = library.template;
  return expandMapped({ ...t, key: substitute(t.key, args), value: substitute(t.value, args) }, span, fail);
}

type FunctionTerm = Extract<TypeTerm, { k: "function" }>;
const isLibraryModule = (module: string): boolean => module.startsWith("typescript/lib/");

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
    // The project itself must load: a type package it names, such as
    // `types: ["node"]`, that is not installed leaves its globals undeclared.
    const broken = project.program.getProgramDiagnostics().find(d => d.category === DiagnosticCategory.Error);
    if (broken) throw new DeclarationError([0, 0], `TypeScript reports an error in the project: ${broken.text}`);
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

/** The expression at exactly `span`, the outermost one there. */
function expressionAt(file: SourceFile, span: Span): Node | null {
  const visit = (node: Node): Node | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (node.getStart(file) === span[0] && node.end === span[1] && !ts.isSourceFile(node)) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The primitives among a type's values whose members a read reaches through
 * a wrapper's prototype. */
function primitivesOf(type: Type): PrimitiveKind[] {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  const flags: Record<PrimitiveKind, number> = { string: TypeFlags.StringLike, number: TypeFlags.NumberLike,
    bigint: TypeFlags.BigIntLike, boolean: TypeFlags.BooleanLike };
  return primitiveKinds.filter(kind => parts.some(part => part.flags & flags[kind]));
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
  /** Told each of the client's global type names, at its first reference
   * (`globals`), that TypeScript binds to a library type read at its meaning
   * rather than joining the graph (`LibraryType`). */
  library?: (span: Span, library: LibraryType) => void;
  /** The client uses arrays: `Array.prototype`'s contract joins the graph
   * (`array-prototype.mts`), at `arrays`, the first array the client writes. */
  arrays?: Span;
  /** The overlay `Array.prototype` is read through; tests vary it. */
  arrayOverlay?: readonly OverlayEntry[];
  /** The client uses `async`, `await` or `for...of`: the intrinsics that
   * stand for them (`intrinsics.mts`) join its values, located at the first
   * such construct. */
  intrinsics?: Span;
  /** The client's value references to names it neither imports nor binds:
   * each that TypeScript binds to a global variable, such as Node's
   * `process` or the standard library's `BigInt`, joins its values, read at
   * the members and call signatures those references select
   * (`selectGlobal`). The first reference locates it. */
  globalValues?: readonly Span[];
  /** Told each call of a global that the reviewed overlay reads as a test
   * of the calculus, such as `Array.isArray(e)`, by the call's span. */
  globalTest?: (span: Span, test: NonNullable<GlobalEntry["test"]>) => void;
  /** Told each call of a global that the reviewed overlay reads as a call of
   * an intrinsic, such as `Promise.resolve(v)`, by the call's span, with the
   * intrinsic's name; the intrinsics then join the values. */
  globalIntrinsic?: (span: Span, name: string) => void;
  /** The names the client's ambient declarations bind, `declare function f`,
   * `declare const x: T`, `declare class C`, one span per name (overloads
   * once): each joins its values at the type its declarations state. */
  ambient?: readonly Span[];
  /** The client's element keys that are identifiers, `e[k]`: each that
   * TypeScript binds to a `unique symbol` constant joins the symbols and is
   * reported to `symbolKey` with its index. */
  symbolKeys?: readonly Span[];
  symbolKey?: (span: Span, symbol: number) => void;
  /** The client's member names of reads `X.y` with `X` an identifier: each
   * that TypeScript binds to a static member of a class the client declares
   * at its top level, `X` naming that class, is reported to `staticMember`
   * with the class's name. */
  staticReads?: readonly Span[];
  staticMember?: (span: Span, cls: string) => void;
  /** The client's top-level enum declarations: each must be one TypeScript
   * accepts, and each member, by its span, is reported to `enumMember` with
   * the value TypeScript computes for it, which is the value its emit writes
   * (DESIGN.md, "Enums"), or undefined where it computes none. */
  enums?: readonly Span[];
  enumMember?: (span: Span, value: string | number | undefined) => void;
  /** The client's reads `X.y` and `X["y"]` with `X` an identifier: each that
   * TypeScript binds to a member of a `const enum` the client declares is
   * reported to `constEnumRead` with the member's value, which TypeScript
   * writes in place of the read. */
  constEnumReads?: readonly Span[];
  constEnumRead?: (span: Span, value: string | number) => void;
  /** The receivers of the client's member reads, `e.k` and `e[k]`: each
   * that TypeScript types as a string, number, bigint or boolean, or a union
   * holding one, reads that primitive's members through its wrapper's
   * prototype, whose contract (`array-prototype.mts`) then joins the graph
   * and whose realm value joins the values, located at the first such
   * receiver. */
  memberReceivers?: readonly Span[];
  /** Told each TypeScript error the gate reads while deciding whether a
   * declaration is clean, whether or not it refuses the source: every error
   * TypeScript reports in each file it examines, each once. */
  seen?: (diagnostic: SeenDiagnostic) => void;
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
        for (const d of found)
          options.seen?.({ file: file.fileName, client: file === client, pos: [d.pos, d.end],
            start: file.getLineAndCharacterOfPosition(d.pos),
            end: file.getLineAndCharacterOfPosition(d.end), text: d.text });
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
    // A standard library type read at its meaning (`LibraryType`). Every
    // declaration TypeScript binds the name to must be the library's, so a
    // client that declares its own `Array`, merging into the global one, is
    // read as any other interface.
    const library = (identifier: Identifier, what: string): LibraryType | null => {
      const nodes = (targetOf(checker, identifier)?.declarations ?? []).map(d => d.resolve());
      const types: TypeDeclaration[] = [];
      for (const node of nodes) {
        if (!node || !isLibraryModule(idOf(node.getSourceFile()))) return null;
        if (isTypeDeclaration(node)) types.push(node);
      }
      const [first] = types;
      const name = first?.name?.text;
      if (!first || !name || types.some(t => t.name?.text !== name)) return null;
      const cleanAll = () => types.forEach(part => clean(part, `${idOf(part.getSourceFile())}#${name}`));
      if ((name === "Array" || name === "ReadonlyArray") && types.every(ts.isInterfaceDeclaration)) {
        cleanAll();
        return { k: "array", readonly: name === "ReadonlyArray" };
      }
      let body = types.length === 1 && ts.isTypeAliasDeclaration(first) ? first.type : undefined;
      while (body && ts.isParenthesizedTypeNode(body)) body = body.type;
      if (!body || !ts.isMappedTypeNode(body)) return null;
      cleanAll();
      // The alias's parameters are positional in its template, and its
      // equation may name nothing else. Its bounds are TypeScript's to check
      // at each reference; only string keys expand.
      const source = first.getSourceFile();
      const where = `${idOf(source)}#${name}`;
      const parameters = (first.typeParameters ?? []).map(p => p.name.text);
      const template = mapped({ source, annotation: false,
        fail: (_node, message) => { throw Error(`${message} in ${where} for ${what}`); },
        named: (node, span) => {
          const index = ts.isIdentifier(node.typeName) ? parameters.indexOf(node.typeName.text) : -1;
          if (index < 0 || node.typeArguments?.length) throw Error(`${where} names a type outside its template`);
          return { k: "parameter", index, span };
        } }, body);
      return { k: "mapped", parameters: parameters.length, template };
    };
    // The standard library's `Function`: a value with call or construct code,
    // and nothing more is known. Its declared members are dropped, which is a
    // supertype of TypeScript's `Function`; TypeScript's own special case,
    // that every callable meets it, is the equation.
    const equation = (node: TypeDeclaration): TypeTerm | null => {
      const source = node.getSourceFile();
      const parts = partners.get(node) ?? [node];
      return ts.isInterfaceDeclaration(node) && node.name.text === "Function" && !node.typeParameters?.length &&
        parts.every(part => isLibraryModule(idOf(part.getSourceFile())))
        ? { k: "callable", span: [node.getStart(source), node.end] } : null;
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
          const known = library(name, `${idOf(source)}#${name.text}`);
          if (known) return libraryTerm(known, (part.typeArguments ?? []).map(read), pos,
            message => { throw Error(`${message} in ${what}`); });
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
    // The value TypeScript binds a name to, from every declaration it has.
    // A function declared with overloads is callable at exactly its
    // overloads, the declarations without a body (an implementation's own
    // signature is not callable from outside): the value meets each, so its
    // type is their intersection. A generic function has one signature. An
    // interface or type alias of the same name is the name's other meaning,
    // which a value reference does not denote.
    const valueOf = (declared: readonly Node[], what: string): Omit<ValueRoot, "binding"> => {
      const nodes = declared.filter(n => !ts.isInterfaceDeclaration(n) && !ts.isTypeAliasDeclaration(n));
      const [node] = nodes;
      if (!node) throw Error(`unresolved value ${what}`);
      const source = node.getSourceFile();
      const span: Span = [node.getStart(source), node.end];
      if (nodes.length > 1) {
        const overloads = nodes.filter((n): n is ts.FunctionDeclaration => ts.isFunctionDeclaration(n) && !n.body);
        if (!overloads.length || !nodes.every(ts.isFunctionDeclaration) || nodes.length - overloads.length > 1)
          throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
        if (overloads.length > 1) {
          if (overloads.some(o => o.typeParameters?.length))
            throw Error(`an overloaded generic function is outside the fragment: ${what}`);
          const forms = overloads.flatMap(o => {
            const at: Span = [o.getStart(source), o.end];
            for (const part of [...o.parameters, ...(o.type ? [o.type] : [])])
              clean(part, `${idOf(source)}#${o.name?.text ?? what}`);
            return signatures(valueScope(o, what), o.parameters, o.type, o, at, true);
          });
          return { declaration: { module: idOf(source), name: overloads[0]?.name?.text ?? what, span },
            construct: false, typeParams: [], type: oneTerm(forms, span) };
        }
        return valueOf(overloads, what);
      }
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
          throw Error(`a declared value must be an annotated constant, function or class: ${what}`);
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
        return { declaration: identity, construct: true, typeParams, type: { k: "constructor", params, rest: null,
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
        // A function with overloads is its several declarations; any other
        // name must have one.
        const nodes = resolveDeclarations(binding.local, binding.local.text);
        const [node] = nodes;
        if (!node || (nodes.length > 1 && !nodes.every(ts.isFunctionDeclaration)))
          throw Error(`TypeScript found ${nodes.length} declarations for ${binding.local.text}`);
        // A class is a type and, imported as a value, a constructor too.
        if (!binding.typeOnly && !(ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)))
          values.push({ binding: { local: binding.local.text, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...valueOf(nodes, binding.local.text) });
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
    // The client's ambient declarations (DESIGN.md, "Ambient declarations"):
    // each name joins the values like an import of the client's own
    // declaration, at the type it states. Nothing runs them.
    for (const span of options.ambient ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript ambient declaration missing");
      const statement = client.statements.find(s => s.pos <= identifier.pos && identifier.end <= s.end);
      const at: Span = statement ? [statement.getStart(client), statement.end] : span;
      try {
        values.push({ binding: { local: identifier.text, imported: identifier.text, specifier: ambientSpecifier,
          span: at }, ...valueOf(resolveDeclarations(identifier, identifier.text), identifier.text) });
      } catch (error) {
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
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
        const known = library(identifier, identifier.text);
        if (known) {
          options.library?.(span, known);
          continue;
        }
        const node = lookup(identifier, identifier.text);
        roots.push({ node, root: { binding: { kind: "global", local: identifier.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    // The prototypes' contracts, `Array.prototype`'s and the primitive
    // wrappers', read before the graph is collected so that the library
    // interfaces they name join it.
    // A standard library interface by name, as the overlays name one: its
    // merged declarations, each clean, the first its identity.
    const libraryInterface = (name: string): TypeDeclaration => {
      const symbol = checker.resolveName(name, SymbolFlags.Interface, client, false);
      const parts = (symbol?.declarations ?? []).map(d => d.resolve())
        .filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
      const [first] = parts;
      if (!first || !parts.every(part => isLibraryModule(idOf(part.getSourceFile()))))
        throw Error(`the standard library declares no ${name}`);
      for (const part of parts) clean(part, `${idOf(part.getSourceFile())}#${name}`);
      partners.set(first, parts);
      return first;
    };
    // A reference to one, at `args`, from a statement of the overlay of
    // library globals: the interface joins the graph.
    const libraryReference = (name: string, args: TypeTerm[]): TypeTerm => {
      const node = libraryInterface(name);
      valueStarts.push(node);
      const target = identityOf(node);
      return { k: "reference", reference: { name, span: [0, 0], arguments: args.map(() => [0, 0] as Span), target },
        args, span: [0, 0] };
    };
    const overlayLibrary: OverlayLibrary = {
      symbol: symbolOf,
      reference: (node, args, span) => {
        valueStarts.push(node);
        const target = identityOf(node);
        return { k: "reference", reference: { name: target.name, span, arguments: args.map(() => span),
          target }, args, span };
      },
    };
    let arrayProto: TypeDefinition | null = null;
    if (options.arrays) {
      try {
        arrayProto = arrayPrototype(checker, client, overlayLibrary, options.arrayOverlay ?? overlay);
      } catch (error) {
        throw new DeclarationError(options.arrays, error instanceof Error ? error.message : String(error));
      }
    }
    // A primitive's members are read through its wrapper's prototype: its
    // contract joins the definitions, and the realm's prototype the values,
    // an assumption at that contract as an import is at its type.
    const primitiveProtos: TypeDefinition[] = [];
    const primitives = new Map<PrimitiveKind, Span>();
    for (const span of options.memberReceivers ?? []) {
      const receiver = expressionAt(client, span);
      if (!receiver) throw new DeclarationError(span, "TypeScript member receiver missing");
      const type = checker.getTypeAtLocation(receiver);
      for (const kind of type ? primitivesOf(type) : [])
        if (!primitives.has(kind)) primitives.set(kind, span);
    }
    for (const [kind, at] of primitives) {
      try {
        const definition = primitivePrototype(checker, client, overlayLibrary, kind);
        primitiveProtos.push(definition);
        const name = primitivePrototypeName(kind);
        values.push({ binding: { local: name, imported: name, specifier: prototypeSpecifier, span: at },
          declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: definition.declaration.name, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
      }
    }
    // `async`, `await` and `for...of`, as the intrinsics that stand for them
    // (`intrinsics.mts`): trusted steps at their signatures, listed as values
    // like an import's.
    // Listed once, located at the first construct or overlay entry that uses
    // them.
    let intrinsicsListed = false;
    const listIntrinsics = (at: Span): void => {
      if (intrinsicsListed) return;
      intrinsicsListed = true;
      try {
        const symbol = checker.resolveName("Promise", SymbolFlags.Interface, client, false);
        const parts = (symbol?.declarations ?? []).map(d => d.resolve())
          .filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
        const [promise] = parts;
        if (!promise) throw Error("the standard library declares no Promise");
        for (const part of parts) clean(part, `${idOf(part.getSourceFile())}#Promise`);
        partners.set(promise, parts);
        valueStarts.push(promise);
        const target = identityOf(promise);
        for (const intrinsic of intrinsics(argument => ({ k: "reference",
          reference: { name: "Promise", span: [0, 0], arguments: [[0, 0]], target },
          args: [argument], span: [0, 0] })))
          values.push({ binding: { local: intrinsic.name, imported: intrinsic.name,
            specifier: intrinsicModule, span: at },
            declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
            construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
      } catch (error) {
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
      }
    };
    if (options.intrinsics) listIntrinsics(options.intrinsics);
    // Global variables the client reads, such as Node's `process` (DESIGN.md,
    // "Global values"): each joins the values like an import, at a definition
    // of its own, keyed by the variable's declaration, that holds only the
    // members and call signatures the client's references select.
    const selections: TypeDefinition[] = [];
    const groups = new Map<number, Identifier[]>();
    for (const span of options.globalValues ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript global value reference missing");
      const symbol = checker.getSymbolAtLocation(identifier);
      if (!symbol || symbol.flags & SymbolFlags.Alias || checker.isUnknownSymbol(symbol) ||
          checker.isUndefinedSymbol(symbol) || !symbol.declarations.length) continue;
      const nodes = symbol.declarations.map(d => d.resolve());
      if (nodes.some(n => !n || n.getSourceFile().fileName === client.fileName)) continue;
      const group = groups.get(symbol.id);
      if (group) group.push(identifier);
      else groups.set(symbol.id, [identifier]);
    }
    for (const uses of groups.values()) {
      const [first] = uses;
      if (!first) continue;
      const at: Span = [first.getStart(client), first.end];
      try {
        const selection = selectGlobal(checker, uses, { lookup, identityOf: idOf, clean, valueScope, partners,
          overlay: globalsOverlay, test: (span, test) => options.globalTest?.(span, test),
          intrinsic: (span, name) => {
            listIntrinsics(span);
            options.globalIntrinsic?.(span, name);
          },
          library: libraryReference,
          define: definition => {
            const key = (d: TypeDefinition) => `${d.declaration.module}#${d.declaration.name}`;
            if (!selections.some(d => key(d) === key(definition))) selections.push(definition);
          } });
        if (!selection) continue;
        const binding = { local: first.text, imported: first.text, specifier: globalSpecifier, span: at };
        // A global only constructed is its construct signatures, as a class
        // value is; any other is its selection.
        if ("construct" in selection) {
          values.push({ binding, construct: true, ...selection.construct });
          continue;
        }
        const definition = selection.definition;
        selections.push(definition);
        values.push({ binding, declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: first.text, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
      }
    }
    // An element key naming a `unique symbol` constant reads that symbol's
    // key; any other is an ordinary index, left to the expression.
    for (const span of options.symbolKeys ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript element key missing");
      const nodes = targetOf(checker, identifier)?.declarations.map(d => d.resolve()) ?? [];
      const [node] = nodes;
      if (nodes.length !== 1 || !node || !ts.isVariableDeclaration(node) || !node.type ||
          !ts.isTypeOperatorNode(node.type) || node.type.operator !== ts.SyntaxKind.UniqueKeyword)
        continue;
      try {
        options.symbolKey?.(span, symbolOf(identifier));
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    for (const span of options.staticReads ?? []) {
      const name = identifierAt(client, span);
      const access = name?.parent;
      if (!name || !access || !ts.isPropertyAccessExpression(access) || !ts.isIdentifier(access.expression))
        throw new DeclarationError(span, "TypeScript member read missing");
      const members = targetOf(checker, name)?.declarations.map(d => d.resolve()) ?? [];
      const owners = targetOf(checker, access.expression)?.declarations.map(d => d.resolve()) ?? [];
      const [member] = members, [owner] = owners;
      if (members.length === 1 && owners.length === 1 && member && owner &&
          ts.isClassDeclaration(owner) && owner.name && owner.parent === client && member.parent === owner &&
          (ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) &&
          member.modifiers?.some(m => m.kind === ts.SyntaxKind.StaticKeyword))
        options.staticMember?.(span, owner.name.text);
    }
    for (const span of options.enums ?? []) {
      const statement = client.statements.find(s => s.getStart(client) === span[0] && s.end === span[1]);
      if (!statement || !ts.isEnumDeclaration(statement))
        throw new DeclarationError(span, "TypeScript enum declaration missing");
      try {
        clean(statement, `enum ${statement.name.text}`);
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
      for (const member of statement.members)
        options.enumMember?.([member.getStart(client), member.end], checker.getConstantValue(member));
    }
    for (const span of options.constEnumReads ?? []) {
      const access = expressionAt(client, span);
      if (!access || !(ts.isPropertyAccessExpression(access) || ts.isElementAccessExpression(access)) ||
          !ts.isIdentifier(access.expression))
        throw new DeclarationError(span, "TypeScript enum member read missing");
      const owners = targetOf(checker, access.expression)?.declarations.map(d => d.resolve()) ?? [];
      const [owner] = owners;
      const value = checker.getConstantValue(access);
      if (owners.length === 1 && owner && ts.isEnumDeclaration(owner) && owner.parent === client &&
          owner.modifiers?.some(m => m.kind === ts.SyntaxKind.ConstKeyword) && value !== undefined)
        options.constEnumRead?.(span, value);
    }
    const seen = new Set<string>();
    const definitions: TypeDefinition[] = [];
    for (const { root, node: start } of roots) {
      try {
        collect(start, seen, definitions, { lookup, identityOf, symbol: symbolOf, partners, library, equation,
          libraryInterface });
      } catch (error) {
        throw new DeclarationError(root.binding.span,
          error instanceof Error ? error.message : String(error));
      }
    }
    for (const [index, start] of valueStarts.entries()) {
      try {
        collect(start, seen, definitions, { lookup, identityOf, symbol: symbolOf, partners, library, equation,
          libraryInterface });
      } catch (error) {
        throw new DeclarationError(values[Math.min(index, values.length - 1)]?.binding.span ?? [0, 0],
          error instanceof Error ? error.message : String(error));
      }
    }
    definitions.push(...selections, ...primitiveProtos);
    // First, so its row follows the four fixed ones in every table.
    if (arrayProto) definitions.unshift(arrayProto);
    return { roots: roots.map(r => r.root), definitions, values, symbols };
  });
}

/** The specifier of a primitive wrapper's prototype: the realm's, which no
 * import names. */
export const prototypeSpecifier = "prototype";
/** The specifier of a global value's binding: no import names it. */
export const globalSpecifier = "global";
/** The specifier of an ambient declaration's binding, `declare function f`:
 * the client states the value's type and nothing defines it. */
export const ambientSpecifier = "ambient";

type SelectionContext = {
  lookup: (identifier: Identifier, what: string) => TypeDeclaration;
  identityOf: (file: SourceFile) => string;
  clean: (node: Node, what: string) => void;
  valueScope: (node: Node, what: string) => TermScope;
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>;
  /** The reviewed overlay a standard library global is read through. */
  overlay: readonly GlobalEntry[];
  /** Told each call the overlay reads as a test of the calculus. */
  test: (span: Span, test: NonNullable<GlobalEntry["test"]>) => void;
  /** Told each call the overlay reads as a call of an intrinsic. */
  intrinsic: (span: Span, name: string) => void;
  /** Given each declaration a read entry's statement names that no library
   * declares (`GlobalEntry.definitions`). */
  define: (definition: TypeDefinition) => void;
  /** A standard library interface applied to `args`, for a statement that
   * names one (`new Set<T>()` gives a `Set<T>`). */
  library: (name: string, args: TypeTerm[]) => TypeTerm;
};

/**
 * A global variable, such as Node's `process` or the standard library's
 * `BigInt`, read at the members and call signatures the client's references
 * `uses` select (DESIGN.md, "Global values" and "Library globals"). Every
 * reference must read a member by name, `process.m`, or be called,
 * `BigInt(v)`. TypeScript resolves the member on the interface the variable
 * is annotated with, through its heritage and merged declarations, and a
 * call to one of that interface's call signatures. An interface of the same
 * name, `interface BigInt` beside `declare var BigInt`, is the name's type
 * meaning, which a value reference does not denote. The definition, keyed by
 * the variable's first declaration, is an object with one member per name
 * read, and the call signatures the client's calls resolve to:
 *
 * - a method is the overloads TypeScript resolves the client's calls to,
 *   each a host-relative member (so its reference must be called), and a
 *   `this` result is the definition itself, the host;
 * - a property is its signature as declared, read like any declaration's;
 * - a call signature is read as a method's is, with no receiver.
 *
 * Leaving the other members and signatures out gives a supertype of the
 * declared type, since methods are host-relative; nothing else about the
 * members read changes. A member inherited from a generic interface, and a
 * generic, optional or `this`-typed method or call signature, are refused.
 * A global the standard library declares is read only through the reviewed
 * overlay (`library-globals.mts`): each signature read must be listed, and a
 * parameter at which the host would run the client's code is stated at what
 * it accepts without running any.
 *
 * A global the client only constructs, `new Array<T>()`, is instead its
 * construct signatures, as a class value is: each the overlay's statement of
 * it, or, outside the standard library, as declared. A global read only
 * through tests, `Array.isArray(e)`, is no value at all (null).
 */
function selectGlobal(checker: Checker, uses: readonly Identifier[], context: SelectionContext):
    { definition: TypeDefinition } |
    { construct: { declaration: DeclarationIdentity; typeParams: ValueRoot["typeParams"]; type: TypeTerm } } |
    null {
  const [first] = uses;
  if (!first) throw Error("a global value without a reference");
  const name = first.text;
  const declarations = (checker.getSymbolAtLocation(first)?.declarations ?? []).map(d => d.resolve());
  const variables = declarations.filter((d): d is ts.VariableDeclaration =>
    !!d && ts.isVariableDeclaration(d) && !!d.type && ts.isIdentifier(d.name));
  const [declaration] = variables;
  if (!declaration || declarations.some(d => !d ||
      (!ts.isInterfaceDeclaration(d) && !variables.includes(d as ts.VariableDeclaration))))
    throw Error(`the global ${name} is not an annotated variable`);
  const where = (node: Node, key: string) => `${context.identityOf(node.getSourceFile())}#${key}`;
  for (const variable of variables) context.clean(variable, where(variable, name));
  const spanOf = (node: Node): Span => [node.getStart(node.getSourceFile()), node.end];
  // A standard library global is read through the reviewed overlay: a
  // signature it does not list, with exactly the text reviewed, is refused.
  const library = variables.every(v => isLibraryModule(context.identityOf(v.getSourceFile())));
  const reviewed = (member: string | undefined, node: Node, what: string):
      (Omit<GlobalEntry, "stated"> & { stated?: Stated }) | undefined => {
    if (!library) return undefined;
    const text = node.getText(node.getSourceFile()).trim();
    const entry = globalEntry(context.overlay, name, member, text);
    if (!entry) throw Error(`${what} is not in the reviewed overlay of library globals: ${text}`);
    for (const definition of entry.definitions ?? []) context.define(definition);
    const stated = entry.stated;
    return { ...entry, stated: typeof stated === "function" ? stated(context.library) : stated };
  };
  // The interface the variable is annotated with, a plain or qualified name.
  const annotation = declaration.type;
  const written = annotation && ts.isTypeReferenceNode(annotation)
    ? ts.isQualifiedName(annotation.typeName) ? annotation.typeName.right : annotation.typeName : null;
  const holder = written && ts.isIdentifier(written) ? context.lookup(written, where(declaration, written.text)) : null;
  if (!holder || !ts.isInterfaceDeclaration(holder) || holder.typeParameters?.length)
    throw Error(`the global ${name} is not annotated with a non-generic interface`);
  const parts = context.partners.get(holder) ?? [holder];
  // A member's declaration is read in its own interface: the variable's, or
  // a base TypeScript found it in, which must bind no type parameters.
  const scopeOf = (member: Node, what: string): TermScope => {
    const owner = member.parent;
    if (!ts.isInterfaceDeclaration(owner)) throw Error(`${what} is not an interface member`);
    if (!parts.includes(owner) && owner.typeParameters?.length)
      throw Error(`${what} is inherited from a generic interface`);
    return context.valueScope(member, what);
  };
  // The declaration among `candidates` TypeScript resolves `call` to.
  const resolvedAmong = <T extends Node>(call: ts.CallExpression | ts.NewExpression, candidates: readonly T[]):
      T | undefined => {
    const resolved = checker.getResolvedSignature(call)?.declaration?.resolve();
    return candidates.find(m => resolved && m.pos === resolved.pos && m.end === resolved.end &&
      m.getSourceFile().fileName === resolved.getSourceFile().fileName);
  };
  // A method's or call signature's forms. A parameter the overlay restricts
  // is stated at what the host accepts: its safe part.
  const forms = (signature: ts.MethodSignatureDeclaration | ts.CallSignatureDeclaration, key: string,
      what: string, entry: GlobalEntry | undefined) => {
    if (signature.typeParameters?.length || (ts.isMethodSignatureDeclaration(signature) &&
        (signature.postfixToken || signature.modifiers?.length)))
      throw Error(`${what} is generic, optional or modified`);
    context.clean(signature, where(signature, key));
    const at = spanOf(signature);
    // `this` as the result is the host: the variable, at this definition.
    const self: TypeTerm = { k: "self", span: at };
    const given = signature.type?.kind === ts.SyntaxKind.ThisType ? self : undefined;
    const read = signatures(scopeOf(signature, what), signature.parameters, signature.type, signature, at, false,
      given);
    const admit = entry?.admit;
    if (!admit) return read;
    const index = signature.parameters.findIndex(p => ts.isIdentifier(p.name) && p.name.text === admit.parameter);
    const parameter = signature.parameters[index];
    if (!parameter || parameter.dotDotDotToken) throw Error(`${what} has no parameter ${admit.parameter}`);
    const stated: TypeTerm[] = admit.safe.map(atom => ({ k: "atom", name: atom, span: at }));
    if (parameter.questionToken && !admit.safe.includes("undefined"))
      stated.push({ k: "atom", name: "undefined", span: at });
    const [only] = stated;
    const type: TypeTerm = stated.length === 1 && only ? only : { k: "union", parts: stated, span: at };
    return read.map(form => ({ ...form, params: form.params.map((p, i) => i === index ? type : p) }));
  };
  const type = checker.getTypeAtLocation(first);
  if (!type) throw Error(`TypeScript gives ${name} no type`);
  const keys = new Map<string, ts.PropertyAccessExpression[]>();
  const calls: ts.CallExpression[] = [];
  const constructs: ts.NewExpression[] = [];
  for (const use of uses) {
    const parent = use.parent;
    if (ts.isPropertyAccessExpression(parent) && parent.expression === use && !parent.questionDotToken &&
        ts.isIdentifier(parent.name))
      keys.set(parent.name.text, [...keys.get(parent.name.text) ?? [], parent]);
    else if (ts.isCallExpression(parent) && parent.expression === use && !parent.questionDotToken)
      calls.push(parent);
    else if (ts.isNewExpression(parent) && parent.expression === use)
      constructs.push(parent);
    else if (ts.isBinaryExpression(parent) && parent.right === use &&
        parent.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) {
      // `e instanceof X`, read only where the overlay states it as a test of
      // the calculus, against the variable's declaration as reviewed.
      const entry = reviewed(undefined, declaration, `${name} as the right operand of instanceof`);
      if (!entry?.test) throw Error(`${name} is not read as an instanceof test`);
      context.test(spanOf(parent), entry.test);
    }
    else throw Error(`${name} is read only through its members, each by name, called or constructed`);
  }
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const [key, accesses] of keys) {
    const what = `${name}.${key}`;
    const nodes = (checker.getPropertyOfType(type, key)?.declarations ?? []).map(d => d.resolve());
    const methods = nodes.filter((d): d is ts.MethodSignatureDeclaration => !!d && ts.isMethodSignatureDeclaration(d));
    const [property] = nodes;
    if (methods.length && methods.length === nodes.length) {
      const chosen = new Map<ts.MethodSignatureDeclaration, ts.CallExpression[]>();
      for (const access of accesses) {
        const call = access.parent;
        if (!ts.isCallExpression(call) || call.expression !== access || call.questionDotToken)
          throw Error(`the method ${what} is only called, on its host`);
        const overload = resolvedAmong(call, methods);
        if (!overload) throw Error(`TypeScript resolves the call of ${what} to no overload it declares`);
        chosen.set(overload, [...chosen.get(overload) ?? [], call]);
      }
      const selected = [...chosen].flatMap(([overload, calls]) => {
        const entry = reviewed(key, overload, what);
        // A test of the calculus: each call is reported, and the member
        // joins no value.
        if (entry?.test) {
          for (const call of calls) {
            const [argument, ...more] = call.arguments;
            if (!argument || more.length || ts.isSpreadElement(argument) || call.typeArguments?.length)
              throw Error(`${what} is a test of one argument`);
            context.test(spanOf(call), entry.test);
          }
          return [];
        }
        // A call of an intrinsic stating the same step: each call is
        // reported, with its arguments as written, and the member joins no
        // value. Explicit type arguments are TypeScript's instance of the
        // declaration; the intrinsic's is proposed and checked on its own.
        if (entry?.intrinsic) {
          for (const call of calls) {
            if (call.arguments.some(ts.isSpreadElement))
              throw Error(`${what} is read as an intrinsic, called without spreads`);
            context.intrinsic(spanOf(call), entry.intrinsic);
          }
          return [];
        }
        // A signature the overlay states instead of the declared one: its
        // parameters bound the arguments, as for a construct.
        if (entry?.stated) {
          const stated = entry.stated;
          for (const call of calls)
            if (call.arguments.length > stated.params.length || call.arguments.some(ts.isSpreadElement))
              throw Error(`${what} is read with at most ${stated.params.length} argument(s)`);
          const at = spanOf(overload);
          const form: FunctionTerm = { k: "function", receiver: { k: "self", span: at }, params: stated.params,
            rest: null, result: stated.result, span: at };
          // A generic statement is a scheme over its binders, as a generic
          // interface method is.
          return [stated.binders.length
            ? { k: "scheme", binders: stated.binders.map(name => ({ name, bound: null, default: null, span: at })),
                signatures: [form], span: at } satisfies TypeTerm
            : form];
        }
        return forms(overload, key, what, entry).map(form => {
          if (form.receiver) throw Error(`the method ${what} states its receiver`);
          return { ...form, receiver: { k: "self", span: form.span } satisfies TypeTerm };
        });
      });
      if (!selected.length) continue;
      const [only] = selected;
      const span = spanOf(accesses[0] ?? first);
      // A generic member is a readonly scheme, and overloads none.
      const scheme = selected.some(form => form.k === "scheme");
      if (scheme && selected.length > 1) throw Error(`${what} selects a generic statement beside other overloads`);
      fields.push({ name: key, optional: false, readonly: scheme, span,
        type: selected.length === 1 && only ? only : { k: "intersection", parts: selected, span } });
    } else if (nodes.length === 1 && property && ts.isPropertySignatureDeclaration(property) && property.type &&
        !property.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword)) {
      const entry = reviewed(key, property, what);
      context.clean(property, where(property, key));
      fields.push({ name: key, optional: property.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
        readonly: property.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
        type: entry?.stated ? entry.stated.result : typeTerm(scopeOf(property, what), property.type, property),
        span: spanOf(property) });
    } else throw Error(`${what} is not one property signature or method signatures`);
  }
  // The call signatures the client's calls of the global resolve to, each
  // once, with the calls that chose it.
  const declared = parts.filter(ts.isInterfaceDeclaration)
    .flatMap(part => part.members.filter(ts.isCallSignatureDeclaration));
  const chosen = new Map<ts.CallSignatureDeclaration, ts.CallExpression[]>();
  for (const call of calls) {
    const signature = resolvedAmong(call, declared);
    if (!signature) throw Error(`TypeScript resolves the call of ${name} to no call signature it declares`);
    chosen.set(signature, [...chosen.get(signature) ?? [], call]);
  }
  const what = `${name}(…)`;
  const callForms = [...chosen].flatMap(([signature, calls]) =>
    forms(signature, name, what, reviewed(undefined, signature, what)).map(form => {
      if (form.receiver) throw Error(`${what} states its receiver`);
      return form;
    }));
  // The construct signatures the client's `new` expressions resolve to, each
  // read as the overlay states it (`stated`), or, outside the standard
  // library, as declared. A stated signature's parameters bound the
  // arguments: the host is stated only at those.
  const declaredNew = parts.filter(ts.isInterfaceDeclaration)
    .flatMap(part => part.members.filter(ts.isConstructSignatureDeclaration));
  const built = new Map<ts.ConstructSignatureDeclaration, ts.NewExpression[]>();
  for (const expression of constructs) {
    const signature = resolvedAmong(expression, declaredNew);
    if (!signature) throw Error(`TypeScript resolves \`new ${name}\` to no construct signature it declares`);
    built.set(signature, [...built.get(signature) ?? [], expression]);
  }
  const whatNew = `new ${name}(…)`;
  const constructForms = [...built].flatMap(([signature, expressions]) => {
    const entry = reviewed(undefined, signature, whatNew);
    const span = spanOf(signature);
    // A construct of an intrinsic stating the same step, `new Promise(e)`:
    // each is reported, with its arguments as written, and joins no value.
    if (entry?.intrinsic) {
      for (const expression of expressions) {
        if (expression.arguments?.some(ts.isSpreadElement))
          throw Error(`${whatNew} is read as an intrinsic, constructed without spreads`);
        context.intrinsic(spanOf(expression), entry.intrinsic);
      }
      return [];
    }
    if (entry?.stated) {
      const stated = entry.stated;
      for (const expression of expressions)
        if ((expression.arguments?.length ?? 0) > stated.params.length ||
            expression.arguments?.some(ts.isSpreadElement))
          throw Error(`${whatNew} is read with at most ${stated.params.length} argument(s)`);
      return [{ binders: stated.binders,
        type: { k: "constructor", params: stated.params, rest: null, result: stated.result, span } satisfies TypeTerm }];
    }
    if (signature.typeParameters?.length) throw Error(`${whatNew} is generic`);
    context.clean(signature, where(signature, name));
    return signatures(scopeOf(signature, whatNew), signature.parameters, signature.type, signature, span, false)
      .map(form => {
        if (form.receiver) throw Error(`${whatNew} states its receiver`);
        return { binders: [] as string[],
          type: { k: "constructor", params: form.params, rest: form.rest, result: form.result, span } satisfies TypeTerm };
      });
  });
  const source = declaration.getSourceFile();
  const identity: DeclarationIdentity = { module: context.identityOf(source), name,
    span: [declaration.getStart(source), declaration.end] };
  if (constructForms.length) {
    if (fields.length || callForms.length)
      throw Error(`${name} is both constructed and read through its members or calls`);
    // Overloads the overlay states alike are one signature.
    const distinct = [...new Map(constructForms.map(f =>
      [JSON.stringify({ ...f, type: { ...f.type, span: null } }), f])).values()];
    const [only] = distinct;
    if (distinct.length === 1 && only)
      return { construct: { declaration: identity, typeParams: only.binders.map(name => ({ name, bound: null })),
        type: only.type } };
    if (distinct.some(f => f.binders.length)) throw Error(`${whatNew} selects several generic signatures`);
    const span = spanOf(first);
    return { construct: { declaration: identity, typeParams: [],
      type: { k: "intersection", parts: distinct.map(f => f.type), span } } };
  }
  // A global read only through tests is not a value.
  if (!fields.length && !callForms.length) return null;
  return { definition: { declaration: identity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: callForms, span: spanOf(first) } } };
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

/** A standard library interface through its overlay entries
 * (`interfaceOverlay`): each listed member, read from the one declaration
 * among the merged parts whose text is the reviewed one, a method as a
 * host-relative member and a property as declared. A member the project's
 * library does not declare is left out. */
function overlaidInterface(node: InterfaceDeclaration, parts: readonly InterfaceDeclaration[],
    entries: readonly OverlayEntry[], scopeOf: (source: SourceFile) => TermScope,
    identityOf: (node: TypeDeclaration) => DeclarationIdentity,
    symbol: (written: Identifier | ts.PropertyAccessExpression) => number,
    library: (name: string, span: Span) => (args: TypeTerm[]) => TypeTerm): TypeTerm {
  const where = `${identityOf(node).module}#${node.name.text}`;
  const keyText = (member: ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration,
      source: SourceFile): string =>
    ts.isIdentifier(member.name) ? member.name.text : member.name.getText(source);
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const entry of entries) {
    const named = parts.flatMap(part => {
      const source = part.getSourceFile();
      return part.members
        .filter((m): m is ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration =>
          (ts.isMethodSignatureDeclaration(m) || ts.isPropertySignatureDeclaration(m)) &&
          keyText(m, source) === entry.name)
        .map(member => ({ member, source }));
    });
    if (!named.length) continue;
    const found = named.filter(({ member, source }) => member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length) throw Error(`${where}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    const { member, source } = only;
    const scope = scopeOf(source);
    const span: Span = [member.getStart(source), member.end];
    const name = member.name;
    const key: PropertyKey = ts.isComputedPropertyName(name) &&
        (ts.isPropertyAccessExpression(name.expression) || ts.isIdentifier(name.expression))
      ? { symbol: symbol(name.expression) } : entry.name;
    if (ts.isPropertySignatureDeclaration(member)) {
      if (!member.type || member.postfixToken ||
          member.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword))
        throw Error(`${where}.${entry.name} is not a plain property`);
      fields.push({ name: key, optional: false, readonly: !!member.modifiers?.length,
        type: typeTerm(scope, member.type, member), span });
      continue;
    }
    if (!ts.isMethodSignatureDeclaration(member) || member.typeParameters?.length || member.postfixToken)
      throw Error(`${where}.${entry.name} is not a plain method`);
    const nameOf = (p: ts.ParameterDeclaration) => ts.isIdentifier(p.name) ? p.name.text : "";
    const parameters = member.parameters.filter(p => !entry.drop?.includes(nameOf(p)));
    // The weaker result: `Iterator` at the declared result's one argument.
    let given: TypeTerm | undefined;
    if (entry.resultAs) {
      const declared = member.type;
      const [argument, ...others] = declared && ts.isTypeReferenceNode(declared) ? declared.typeArguments ?? [] : [];
      if (!argument || others.length) throw Error(`${where}.${entry.name} has no element type to state`);
      given = library(entry.resultAs, span)([typeTerm(scope, argument, member)]);
    } else if (entry.resultIsReceiver) {
      if (member.type?.kind !== ts.SyntaxKind.ThisType) throw Error(`${where}.${entry.name} does not return this`);
      given = { k: "self", span };
    }
    const forms = signatures(scope, parameters, member.type, member, span, false, given);
    if (forms.some(f => f.receiver)) throw Error(`${where}.${entry.name} states its receiver`);
    fields.push({ name: key, optional: false, readonly: false, span,
      type: oneTerm(forms.map(f => ({ ...f, receiver: { k: "self", span } })), span) });
  }
  return { k: "object", fields, stringIndex: null, calls: [], span: identityOf(node).span };
}

/** Every declaration reachable from `start`, each once across roots. */
function collect(start: TypeDeclaration, seen: Set<string>, definitions: TypeDefinition[], context: {
  lookup: (identifier: Identifier, what: string) => TypeDeclaration;
  identityOf: (node: TypeDeclaration) => DeclarationIdentity;
  symbol: (written: Identifier | ts.PropertyAccessExpression) => number;
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>;
  library: (identifier: Identifier, what: string) => LibraryType | null;
  /** A declaration's equation where it is not its declared body. */
  equation: (node: TypeDeclaration) => TypeTerm | null;
  /** The standard library interface of this name, such as `Iterator`. */
  libraryInterface: (name: string) => TypeDeclaration;
}): void {
  const { lookup, identityOf, symbol, partners, library, equation } = context;
  const queue: TypeDeclaration[] = [start];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const node = queue[cursor];
    if (!node) throw Error("missing queued declaration");
    const identity = identityOf(node);
    const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const stated = equation(node);
    if (stated) {
      definitions.push({ declaration: identity, parameters: [], bases: [], expression: stated });
      continue;
    }
    const source = node.getSourceFile();
    const parameterNodes = node.typeParameters ?? [];
    const parameterNames = parameterNodes.map(parameter => parameter.name.text);
    if (new Set(parameterNames).size !== parameterNames.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
    const reference = (source: SourceFile, identifier: Identifier, arguments_: readonly TypeNode[], pos: Span,
        read: (part: TypeNode) => TypeTerm, base = false): TypeTerm => {
      const what = `${identity.module}#${identifier.text}`;
      const known = library(identifier, what);
      // A base is a declaration whose members are inherited; a library type
      // read at its meaning has none here.
      if (known && base)
        throw Error(`extending the standard library's ${identifier.text} is outside the fragment`);
      if (known) return libraryTerm(known, arguments_.map(read), pos,
        message => { throw Error(`${message} in ${identity.module}#${identity.name}`); });
      const targetNode = lookup(identifier, what);
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
    // A standard library interface read through the overlay: only its listed
    // members, and no base.
    const overlaid = ts.isInterfaceDeclaration(node) && Object.hasOwn(interfaceOverlay, node.name.text) &&
        parts.every(part => isLibraryModule(identityOf(part).module))
      ? interfaceOverlay[node.name.text] : undefined;
    if (overlaid && ts.isInterfaceDeclaration(node)) {
      definitions.push({ declaration: identity, parameters, bases: [],
        expression: overlaidInterface(node, parts.filter(ts.isInterfaceDeclaration), overlaid, scopeOf,
          identityOf, symbol, (name, span) => {
          const target = context.libraryInterface(name);
          queue.push(target);
          return (args: TypeTerm[]): TypeTerm => ({ k: "reference", args, span,
            reference: { name, span, arguments: args.map(() => span), target: identityOf(target) } });
        }) });
      continue;
    }
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
              [base.getStart(file), base.end], read, true);
          });
        });
    });
    definitions.push({ declaration: identity, parameters, bases, expression });
  }
}
