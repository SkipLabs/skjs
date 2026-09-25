/** `ArrayProto`, the contract of `Array.prototype`: TypeScript's own
 * declarations of `ReadonlyArray<T>` and `Array<T>`, as the project's standard
 * library states them, through a reviewed overlay. Nothing is vendored. The
 * overlay holds only what those declarations leave out and soundness needs
 * (DESIGN.md, "Where `ArrayProto` comes from"):
 *
 * - which members exist: any member not listed is refused, not trusted;
 * - each member's receiver: `readonly T[]` for one declared on
 *   `ReadonlyArray`, `T[]` for a mutator declared only on `Array`;
 * - parameters dropped (`thisArg?: any`), which calls must then omit;
 * - which overload is kept: one whose declared result the library does not
 *   deliver, such as `reduce(cb): T` on an empty array, is not listed.
 *
 * Each entry records the declaration text it was reviewed against. A member
 * is read only from a declaration with exactly that text, so a changed
 * library is refused here and reviewed again, never trusted silently. */
import { SymbolFlags, type Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { signatures, typeTerm, type TermScope } from "./type-term.mts";
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";

export type OverlayEntry = {
  /** The member's key on `Array.prototype`. */
  name: string;
  /** Where it is declared: `ReadonlyArray` for a member that only reads the
   * array, `Array` for a mutator. */
  from: "ReadonlyArray" | "Array";
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** Parameters dropped by name: calls must omit them. */
  drop?: string[];
  /** The declared `this` result is the receiver. */
  resultIsReceiver?: boolean;
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
  // Not listed: `concat` names `ConcatArray`, and `values`, `keys` and
  // `entries` name `ArrayIterator`, which the overlay does not read yet.
];

/** The synthetic declaration the array types' prototype view names. */
export const arrayProtoIdentity: DeclarationIdentity =
  { module: "skjs/array-prototype", name: "ArrayProto", span: [0, 0] };

/** `ArrayProto` as a declaration: a record of readonly members, each a scheme
 * over the array's element binder `T` and the member's own binders, whose one
 * signature takes the array as its receiver. `at` locates a refusal. */
export function arrayPrototype(checker: Checker, at: Node,
    entries: readonly OverlayEntry[] = overlay): TypeDefinition {
  const declared = (name: "ReadonlyArray" | "Array") => {
    const symbol = checker.resolveName(name, SymbolFlags.Interface, at, false);
    const parts = (symbol?.declarations ?? []).map(d => d.resolve())
      .filter((n): n is ts.InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
    if (!parts.length) throw Error(`the standard library declares no ${name}`);
    return parts;
  };
  const libraries = { ReadonlyArray: declared("ReadonlyArray"), Array: declared("Array") };
  const fields = entries.flatMap(entry => {
    const named = libraries[entry.from].flatMap(part => part.members
      .filter(ts.isMethodSignatureDeclaration)
      .filter(m => ts.isIdentifier(m.name) && m.name.text === entry.name)
      .map(m => ({ member: m, source: part.getSourceFile() })));
    // A member the project's standard library does not declare, as `at`
    // before ES2022, is not part of its `Array.prototype`.
    if (!named.length) return [];
    const found = named.filter(({ member, source }) =>
      member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length)
      throw Error(`${entry.from}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    const { member, source } = only;
    const span: [number, number] = [0, 0];
    const own = (member.typeParameters ?? []).map(p => p.name.text);
    const binders = ["T", ...own];
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
    const element: TypeTerm = { k: "binder", name: "T", span };
    const receiver: TypeTerm = { k: "array", readonly: entry.from === "ReadonlyArray", element, span };
    const parameters = member.parameters.filter(p =>
      !(ts.isIdentifier(p.name) && entry.drop?.includes(p.name.text)));
    const forms = signatures(scope, parameters, member.type, member, span, false,
      entry.resultIsReceiver ? receiver : undefined);
    if (forms.length !== 1 || forms.some(f => f.receiver))
      throw Error(`${entry.from}.${entry.name} is not one signature`);
    const type: TypeTerm = { k: "scheme",
      binders: binders.map(name => ({ name, bound: null, default: null, span })),
      signatures: forms.map(f => ({ ...f, receiver })), span };
    return [{ name: entry.name, optional: false, readonly: true, type, span }];
  });
  return { declaration: arrayProtoIdentity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: [], span: [0, 0] } };
}
