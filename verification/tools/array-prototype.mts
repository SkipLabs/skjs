/** The contracts of the realm's prototypes a program reads members through:
 * `ArrayProto`, the contract of `Array.prototype`, and `StringProto`,
 * `NumberProto`, `BigIntProto` and `BooleanProto`, those of the prototypes a
 * primitive's members are read from (`"a".toUpperCase()`, `n.toString(16)`).
 * Each is TypeScript's own declarations, as the project's standard library
 * states them (`ReadonlyArray<T>` and `Array<T>`; `String`, `Number`, `BigInt`,
 * `Boolean`), through a reviewed overlay. Nothing is vendored. The overlay
 * holds only what those declarations leave out and soundness needs
 * (DESIGN.md, "Where `ArrayProto` comes from", "Primitive members"):
 *
 * - which members exist: any member not listed is refused, not trusted;
 * - each member's receiver: `readonly T[]` for one declared on
 *   `ReadonlyArray`, `T[]` for a mutator declared only on `Array`, the
 *   primitive itself for a primitive's member;
 * - parameters dropped (`thisArg?: any`, `locales`), which calls must then
 *   omit;
 * - parameters narrowed to the domain on which the member does not throw
 *   (`toString(radix)` takes 2 to 36, as a `RangeError` says elsewhere);
 * - which overload is kept: one whose declared result the library does not
 *   deliver, such as `reduce(cb): T` on an empty array, is not listed.
 *
 * Each entry records the declaration text it was reviewed against. A member
 * is read only from a declaration with exactly that text, so a changed
 * library is refused here and reviewed again, never trusted silently. */
import { SymbolFlags, type Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { optionalTerm, signatures, typeTerm, type TermScope } from "./type-term.mts";
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";

export type OverlayEntry = {
  /** The member's key on the prototype, as declared: a name, or a computed
   * key such as `[Symbol.iterator]`. */
  name: string;
  /** Where it is declared: `ReadonlyArray` for a member that only reads the
   * array, `Array` for a mutator; the primitive's own interface, or `Object`
   * for a member TypeScript reads there that the primitive's prototype owns
   * (`Boolean.prototype.toString`). */
  from: string;
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** Parameters dropped by name: calls must omit them. */
  drop?: string[];
  /** Parameters narrowed, by name, to the values on which the member does
   * not throw: a subtype of the declared type, which calls must meet. */
  narrow?: Record<string, TypeTerm>;
  /** The declared `this` result is the receiver. */
  resultIsReceiver?: boolean;
  /** The result stated as this standard library interface at `T`, which the
   * declared result implies: a weaker contract than the declaration's. */
  resultAs?: "Iterator";
};

export const overlay: readonly OverlayEntry[] = [
  { name: "forEach", from: "ReadonlyArray",
    signature: "forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, thisArg?: any): void;",
    drop: ["thisArg"] },
  { name: "map", from: "ReadonlyArray",
    signature: "map<U>(callbackfn: (value: T, index: number, array: readonly T[]) => U, thisArg?: any): U[];",
    drop: ["thisArg"] },
  // Only the overload with an initial value: without one, an empty array
  // throws where the declaration promises a `T`.
  { name: "reduce", from: "ReadonlyArray",
    signature: "reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  { name: "reduceRight", from: "ReadonlyArray",
    signature: "reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  // Arrays are dense, so a callback sees only elements. The predicate-typed
  // overloads (`value is S`) are not listed.
  { name: "every", from: "ReadonlyArray",
    signature: "every(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    drop: ["thisArg"] },
  { name: "some", from: "ReadonlyArray",
    signature: "some(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    drop: ["thisArg"] },
  { name: "filter", from: "ReadonlyArray",
    signature: "filter(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): T[];",
    drop: ["thisArg"] },
  { name: "slice", from: "ReadonlyArray", signature: "slice(start?: number, end?: number): T[];" },
  { name: "join", from: "ReadonlyArray", signature: "join(separator?: string): string;" },
  { name: "indexOf", from: "ReadonlyArray",
    signature: "indexOf(searchElement: T, fromIndex?: number): number;" },
  { name: "lastIndexOf", from: "ReadonlyArray",
    signature: "lastIndexOf(searchElement: T, fromIndex?: number): number;" },
  { name: "includes", from: "ReadonlyArray",
    signature: "includes(searchElement: T, fromIndex?: number): boolean;" },
  { name: "at", from: "ReadonlyArray", signature: "at(index: number): T | undefined;" },
  { name: "find", from: "ReadonlyArray",
    signature: "find(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): T | undefined;",
    drop: ["thisArg"] },
  { name: "findIndex", from: "ReadonlyArray",
    signature: "findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): number;",
    drop: ["thisArg"] },
  // Mutators take a mutable array.
  { name: "sort", from: "Array",
    signature: "sort(compareFn?: (a: T, b: T) => number): this;", resultIsReceiver: true },
  { name: "push", from: "Array", signature: "push(...items: T[]): number;" },
  { name: "pop", from: "Array", signature: "pop(): T | undefined;" },
  { name: "shift", from: "Array", signature: "shift(): T | undefined;" },
  { name: "unshift", from: "Array", signature: "unshift(...items: T[]): number;" },
  { name: "reverse", from: "Array", signature: "reverse(): T[];" },
  // Iteration: `ArrayIterator<T>` extends `IteratorObject<T,
  // BuiltinIteratorReturn, unknown>`, an `Iterator<T, BuiltinIteratorReturn,
  // unknown>`, which meets `Iterator<T>`, the result `Iterable<T>` asks for.
  { name: "[Symbol.iterator]", from: "ReadonlyArray",
    signature: "[Symbol.iterator](): ArrayIterator<T>;", resultAs: "Iterator" },
  // Not listed: `concat` names `ConcatArray`, and `values`, `keys` and
  // `entries` are not needed yet.
];

/** The integers `from` to `to` as a union of literal types. */
const integers = (from: number, to: number): TypeTerm => ({ k: "union", span: [0, 0],
  parts: Array.from({ length: to - from + 1 }, (_, i) =>
    ({ k: "literal", name: "number", text: String(from + i), span: [0, 0] })) });
/** A radix `toString` accepts: `ToIntegerOrInfinity` of any other throws. */
const radix = integers(2, 36);

/** The members of the primitive wrappers' prototypes. Each is an own property
 * of that prototype (so `String.prototype.toLocaleString`, which is
 * `Object.prototype`'s, is not listed). Not listed: members that throw on
 * arguments their declaration admits and no narrowing states simply
 * (`repeat`, `normalize(form?: string)`), members that name `RegExp` or a
 * callback typed with `any` (`replace`, `match`, `search`, `split`), and
 * members taking locales (their `RangeError`s), whose `locales` and `options`
 * are dropped where the member is kept. A string owns `length` and its
 * indices, which are not the prototype's. */
export const primitiveOverlay: Readonly<Record<PrimitiveKind, readonly OverlayEntry[]>> = {
  string: [
    { name: "toString", from: "String", signature: "toString(): string;" },
    { name: "valueOf", from: "String", signature: "valueOf(): string;" },
    { name: "charAt", from: "String", signature: "charAt(pos: number): string;" },
    { name: "charCodeAt", from: "String", signature: "charCodeAt(index: number): number;" },
    { name: "concat", from: "String", signature: "concat(...strings: string[]): string;" },
    { name: "indexOf", from: "String", signature: "indexOf(searchString: string, position?: number): number;" },
    { name: "lastIndexOf", from: "String",
      signature: "lastIndexOf(searchString: string, position?: number): number;" },
    { name: "localeCompare", from: "String", signature: "localeCompare(that: string): number;" },
    { name: "slice", from: "String", signature: "slice(start?: number, end?: number): string;" },
    { name: "substring", from: "String", signature: "substring(start: number, end?: number): string;" },
    { name: "toLowerCase", from: "String", signature: "toLowerCase(): string;" },
    { name: "toUpperCase", from: "String", signature: "toUpperCase(): string;" },
    { name: "trim", from: "String", signature: "trim(): string;" },
    { name: "includes", from: "String", signature: "includes(searchString: string, position?: number): boolean;" },
    { name: "startsWith", from: "String",
      signature: "startsWith(searchString: string, position?: number): boolean;" },
    { name: "endsWith", from: "String", signature: "endsWith(searchString: string, endPosition?: number): boolean;" },
    { name: "normalize", from: "String", signature: "normalize(form: \"NFC\" | \"NFD\" | \"NFKC\" | \"NFKD\"): string;" },
    { name: "codePointAt", from: "String", signature: "codePointAt(pos: number): number | undefined;" },
    { name: "trimStart", from: "String", signature: "trimStart(): string;" },
    { name: "trimEnd", from: "String", signature: "trimEnd(): string;" },
    { name: "at", from: "String", signature: "at(index: number): string | undefined;" },
  ],
  number: [
    { name: "toString", from: "Number", signature: "toString(radix?: number): string;", narrow: { radix } },
    { name: "valueOf", from: "Number", signature: "valueOf(): number;" },
    // Each throws a `RangeError` outside these digit counts.
    { name: "toFixed", from: "Number", signature: "toFixed(fractionDigits?: number): string;",
      narrow: { fractionDigits: integers(0, 100) } },
    { name: "toExponential", from: "Number", signature: "toExponential(fractionDigits?: number): string;",
      narrow: { fractionDigits: integers(0, 100) } },
    { name: "toPrecision", from: "Number", signature: "toPrecision(precision?: number): string;",
      narrow: { precision: integers(1, 100) } },
    { name: "toLocaleString", from: "Number",
      signature: "toLocaleString(locales?: string | string[], options?: Intl.NumberFormatOptions): string;",
      drop: ["locales", "options"] },
  ],
  bigint: [
    { name: "toString", from: "BigInt", signature: "toString(radix?: number): string;", narrow: { radix } },
    { name: "valueOf", from: "BigInt", signature: "valueOf(): bigint;" },
    { name: "toLocaleString", from: "BigInt",
      signature: "toLocaleString(locales?: Intl.LocalesArgument, options?: BigIntToLocaleStringOptions): string;",
      drop: ["locales", "options"] },
  ],
  boolean: [
    { name: "valueOf", from: "Boolean", signature: "valueOf(): boolean;" },
    // TypeScript reads it from `Object`; `Boolean.prototype` owns it.
    { name: "toString", from: "Object", signature: "toString(): string;" },
  ],
};

/** What the overlay reads through the declaration graph: the symbol a
 * computed key names, and a reference to a standard library interface, which
 * then joins the graph. */
export type OverlayLibrary = {
  symbol: (written: ts.PropertyAccessExpression | ts.Identifier) => number;
  reference: (node: ts.InterfaceDeclaration, args: TypeTerm[], span: [number, number]) => TypeTerm;
};

/** The synthetic declaration the array types' prototype view names. */
export const arrayProtoIdentity: DeclarationIdentity =
  { module: "skjs/array-prototype", name: "ArrayProto", span: [0, 0] };

/** A primitive whose members are read through its wrapper's prototype. */
export type PrimitiveKind = "string" | "number" | "bigint" | "boolean";
export const primitiveKinds: readonly PrimitiveKind[] = ["string", "number", "bigint", "boolean"];
const wrapperName: Record<PrimitiveKind, string> =
  { string: "String", number: "Number", bigint: "BigInt", boolean: "Boolean" };

/** The synthetic declaration of a primitive's prototype contract, and the
 * module value holding the realm's prototype at it, a name no source
 * identifier spells. */
export const primitiveProtoIdentity = (kind: PrimitiveKind): DeclarationIdentity =>
  ({ module: `skjs/${kind}-prototype`, name: `${wrapperName[kind]}Proto`, span: [0, 0] });
export const primitivePrototypeName = (kind: PrimitiveKind): string =>
  `[[${wrapperName[kind]}.prototype]]`;

/** One prototype's contract: its declaration, its own binders (the array's
 * element `T`), and the receiver a member declared on an interface takes. */
type Prototype = {
  identity: DeclarationIdentity;
  binders: string[];
  receiver: (from: string) => TypeTerm;
  entries: readonly OverlayEntry[];
};

/** `ArrayProto` as a declaration: a record of readonly members, each a scheme
 * over the array's element binder `T` and the member's own binders, whose one
 * signature takes the array as its receiver. `at` locates a refusal. */
export function arrayPrototype(checker: Checker, at: Node, library: OverlayLibrary,
    entries: readonly OverlayEntry[] = overlay): TypeDefinition {
  const element: TypeTerm = { k: "binder", name: "T", span: [0, 0] };
  return prototype(checker, at, library, { identity: arrayProtoIdentity, binders: ["T"], entries,
    receiver: from => ({ k: "array", readonly: from === "ReadonlyArray", element, span: [0, 0] }) });
}

/** A primitive's prototype contract, `StringProto` for `String.prototype`: a
 * record of readonly members, each of whose signatures takes the primitive
 * as its receiver. */
export function primitivePrototype(checker: Checker, at: Node, library: OverlayLibrary,
    kind: PrimitiveKind, entries: readonly OverlayEntry[] = primitiveOverlay[kind]): TypeDefinition {
  // A string's own keys are its `length` and its indices: never the prototype's.
  const owned = entries.find(e => kind === "string" && (e.name === "length" || /^\d/.test(e.name)));
  if (owned) throw Error(`a string owns '${owned.name}'; String.prototype's does not answer for it`);
  return prototype(checker, at, library, { identity: primitiveProtoIdentity(kind), binders: [], entries,
    receiver: () => ({ k: "atom", name: kind, span: [0, 0] }) });
}

function prototype(checker: Checker, at: Node, library: OverlayLibrary, proto: Prototype): TypeDefinition {
  const declared = (name: string) => {
    const symbol = checker.resolveName(name, SymbolFlags.Interface, at, false);
    const parts = (symbol?.declarations ?? []).map(d => d.resolve())
      .filter((n): n is ts.InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
    if (!parts.length) throw Error(`the standard library declares no ${name}`);
    return parts;
  };
  const libraries = new Map<string, ts.InterfaceDeclaration[]>();
  const libraryOf = (name: string) => {
    const known = libraries.get(name);
    if (known) return known;
    const parts = declared(name);
    libraries.set(name, parts);
    return parts;
  };
  const interfaceOf = (name: "Iterator") => {
    const [first] = declared(name);
    if (!first) throw Error(`the standard library declares no ${name}`);
    return first;
  };
  const fields = proto.entries.flatMap(entry => {
    const named = libraryOf(entry.from).flatMap(part => part.members
      .filter(ts.isMethodSignatureDeclaration)
      .filter(m => (ts.isIdentifier(m.name) ? m.name.text : m.name.getText(part.getSourceFile())) === entry.name)
      .map(m => ({ member: m, source: part.getSourceFile() })));
    // A member the project's standard library does not declare, as `at`
    // before ES2022, is not part of its prototype.
    if (!named.length) return [];
    const found = named.filter(({ member, source }) =>
      member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length)
      throw Error(`${entry.from}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    const { member, source } = only;
    const span: [number, number] = [0, 0];
    const own = (member.typeParameters ?? []).map(p => p.name.text);
    // The member's own binders lead, as its declaration lists them, so an
    // explicit type argument list instantiates them in order; the
    // prototype's binders follow, fixed by the receiver.
    const binders = [...own, ...proto.binders];
    const scope: TermScope = {
      source: source as SourceFile,
      annotation: false,
      fail: (_node, message) => { throw Error(`${message} in ${entry.from}.${entry.name}`); },
      named: (node, pos) => {
        if (ts.isIdentifier(node.typeName) && binders.includes(node.typeName.text) &&
            !node.typeArguments?.length)
          return { k: "binder", name: node.typeName.text, span: pos };
        throw Error(`${entry.from}.${entry.name} names a type the overlay does not read`);
      },
    };
    const receiver = proto.receiver(entry.from);
    const nameOf = (p: ts.ParameterDeclaration) => ts.isIdentifier(p.name) ? p.name.text : "";
    const parameters = member.parameters.filter(p => !entry.drop?.includes(nameOf(p)));
    // A narrowed parameter is not read from its declaration: it takes its
    // place at the narrowed type, optional where declared so.
    const narrowed = parameters.map(p => entry.narrow?.[nameOf(p)]);
    const stated = entry.resultAs
      ? library.reference(interfaceOf(entry.resultAs), [{ k: "binder", name: "T", span }], span)
      : entry.resultIsReceiver ? receiver : undefined;
    const forms = signatures(scope, parameters.filter((_, i) => !narrowed[i]),
      entry.resultAs ? undefined : member.type, member, span, false, stated);
    if (forms.length !== 1 || forms.some(f => f.receiver))
      throw Error(`${entry.from}.${entry.name} is not one signature`);
    const narrowedForms = forms.map(f => {
      const params = [...f.params];
      parameters.forEach((p, i) => {
        const narrow = narrowed[i];
        if (!narrow) return;
        if (p.dotDotDotToken) throw Error(`${entry.from}.${entry.name} narrows a rest parameter`);
        params.splice(i, 0, p.questionToken ? optionalTerm(narrow, span) : narrow);
      });
      return { ...f, params };
    });
    const type: TypeTerm = binders.length
      ? { k: "scheme", binders: binders.map(name => ({ name, bound: null, default: null, span })),
          signatures: narrowedForms.map(f => ({ ...f, receiver })), span }
      : { ...narrowedForms[0]!, receiver };
    const key = ts.isComputedPropertyName(member.name) &&
        (ts.isPropertyAccessExpression(member.name.expression) || ts.isIdentifier(member.name.expression))
      ? { symbol: library.symbol(member.name.expression) } : entry.name;
    return [{ name: key, optional: false, readonly: true, type, span }];
  });
  return { declaration: proto.identity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: [], span: [0, 0] } };
}
