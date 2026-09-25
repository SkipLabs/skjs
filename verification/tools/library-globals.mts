/** The standard library's global values, such as `BigInt` and `Symbol`, as a
 * client may use them: TypeScript's own declarations, as the project's
 * standard library states them, through a reviewed overlay (DESIGN.md,
 * "Library globals"). Nothing is vendored. As for `Array.prototype`
 * (`array-prototype.mts`), the overlay holds only what those declarations do
 * not say and soundness needs:
 *
 * - which signatures exist: a global's call, construct, method or property
 *   signature is read only when an entry lists it, with exactly the text it
 *   was reviewed against, so a changed library is refused and reviewed again;
 * - where the host throws on an argument the declaration admits, the
 *   parameter the reader states instead: the part of the declared type at
 *   which the host cannot throw, and each literal argument the client passes
 *   that the host accepts (`admit`). A throw is a stuck term in the calculus,
 *   so a signature promising a result there would be false;
 * - where the declaration states less than the host does (`any`) or more (a
 *   parameter at which it misbehaves), the signature the host meets, stated
 *   instead (`stated`);
 * - a member whose call is a primitive of the calculus: a test (`test`) or
 *   a trusted step already stated as an intrinsic (`intrinsic`).
 *
 * A global declared outside the standard library, such as Node's `process`,
 * is read as its declaration states, member by member (`selectGlobal`). */
import type { TypeTerm } from "./declaration-types.mts";
import { asyncCompleteName, asyncReturnName, promiseAllName } from "./intrinsics.mts";

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];

export type GlobalEntry = {
  /** The global variable, `declare var BigInt: BigIntConstructor`. */
  global: string;
  /** The member read, `Symbol.for`; absent for a call of the global itself. */
  member?: string;
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** A parameter the host rejects some declared arguments of: it is stated
   * as `safe`, joined by each literal argument of the client's calls that
   * `literal` accepts (a number or string literal type TypeScript gives the
   * argument). */
  admit?: { parameter: string; safe: AtomName[]; literal: (value: string | number) => boolean };
  /** The call is a test of the calculus, not a call of the member: the
   * parser writes `Array.isArray(e)` as the test `isArray` of `e`, whose
   * narrowing Lean proves, and the member joins no value. */
  test?: "isArray";
  /** The call is a call of this intrinsic (`intrinsics.mts`), which states
   * the same step: the parser writes `Promise.resolve(v)` as
   * `%AsyncReturn%(v)`, and the member joins no value. */
  intrinsic?: string;
  /** The signature read instead of the declared one: its own binders, its
   * parameters, which a call may not exceed, and its result. What the host
   * does at these arguments, stated as a type. For a property, its type is
   * the result. */
  stated?: { binders: string[]; params: TypeTerm[]; result: TypeTerm };
};

const at: [number, number] = [0, 0];
const binder = (name: string): TypeTerm => ({ k: "binder", name, span: at });
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });

/** `BigInt(v)` throws a RangeError for a number that is not an integer and a
 * SyntaxError for a string that is not an integer's spelling. A bigint or a
 * Boolean always converts; an integer or a string literal is admitted when
 * the host converts it, which is decided by converting it. */
const bigintLiteral = (value: string | number): boolean => {
  if (typeof value === "number") return Number.isInteger(value);
  try {
    BigInt(value);
    return true;
  } catch {
    return false;
  }
};

export const globalsOverlay: readonly GlobalEntry[] = [
  // Output, which the model does not observe. The host formats each argument
  // without running client code the fragment can write (no getters, no
  // symbol-keyed methods such as a custom inspection), and returns
  // `undefined`. `any` is read as `unknown`, so any argument is admitted.
  { global: "console", member: "log", signature: "log(...data: any[]): void;" },
  { global: "BigInt", signature: "(value: bigint | boolean | number | string): bigint;",
    admit: { parameter: "value", safe: ["bigint", "boolean"], literal: bigintLiteral } },
  // A new symbol whose description is the argument converted to a string,
  // which a string or number never fails.
  { global: "Symbol", signature: "(description?: string | number): symbol;" },
  { global: "Symbol", member: "for", signature: "for(key: string): symbol;" },
  { global: "Symbol", member: "keyFor", signature: "keyFor(sym: symbol): string | undefined;" },
  // The well-known symbols, each a symbol: stated at `symbol`, since the
  // reader has no `unique symbol` type of a library property. Which symbol
  // each is, a key the library's types use, is not read.
  ...["iterator", "asyncIterator", "hasInstance", "toPrimitive", "toStringTag"].map(
    (member): GlobalEntry => ({ global: "Symbol", member, signature: `readonly ${member}: unique symbol;`,
      stated: { binders: [], params: [], result: atom("symbol") } })),
  // `String(v)` converts a primitive, a symbol included, without running
  // client code; an object's conversion calls its `toString` or `valueOf`,
  // which may throw or return an object, and then `String` throws.
  { global: "String", signature: "(value?: any): string;",
    admit: { parameter: "value", safe: ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"],
      literal: () => false } },
  // A fresh array of the object's own enumerable string keys: true of every
  // object, whatever its type says of its keys, and it runs no client code
  // (no getter is called). ES5 declares it at `object`, ES2015 at `{}`.
  { global: "Object", member: "keys", signature: "keys(o: object): string[];" },
  { global: "Object", member: "keys", signature: "keys(o: {}): string[];" },
  // The values of those keys, and the key-value pairs: nothing is known of
  // them, `any` read as `unknown`, and each pair is a fresh array. Reading a
  // value runs an accessor's getter: the fragment writes none, and a host
  // object's is assumed to return. The generic overloads,
  // `values<T>(o: { [s: string]: T } | ArrayLike<T>)`, which TypeScript
  // selects for a record type whose keys it does not bound, are not listed.
  { global: "Object", member: "values", signature: "values(o: {}): any[];" },
  { global: "Object", member: "entries", signature: "entries(o: {}): [string, any][];" },
  // A test of the array's identity, which the calculus makes itself
  // (`Tag.isArray`): true of exactly the objects that own an array store,
  // JavaScript's Array exotic objects. The declared guard, `arg is any[]`,
  // is not read: Lean narrows by the clauses of the tested value's type.
  { global: "Array", member: "isArray", signature: "isArray(arg: any): arg is any[];", test: "isArray" },
  // `new Array()` and `new Array<T>()` are a fresh empty array, which is a
  // `T[]` at every `T`: the non-generic declaration's `any[]` states less
  // than that. An argument is refused: a single number is a length, and the
  // array it makes has holes, which an array type here promises it has not.
  ...["new (arrayLength?: number): any[];", "new <T>(...items: T[]): T[];"].map(
    (signature): GlobalEntry => ({ global: "Array", signature,
      stated: { binders: ["T"], params: [], result: { k: "array", readonly: false, element: binder("T"), span: at } } })),
  // `new Error(m)` with a string owns `message`, that string; its `name`
  // and a missing message are `Error.prototype`'s, which the model does not
  // hold, so only the own field is stated, and the message is required.
  // `stack` is the engine's and is not stated. ES2022 adds `options`.
  ...["new (message?: string): Error;", "new (message?: string, options?: ErrorOptions): Error;"].map(
    (signature): GlobalEntry => ({ global: "Error", signature,
      stated: { binders: [], params: [atom("string")],
        result: { k: "object", fields: [{ name: "message", optional: false, readonly: true,
          type: atom("string"), span: at }], stringIndex: null, calls: [], span: at } } })),
  // A promise settled to the value, as an async function's return is: the
  // intrinsic `%AsyncReturn%`, whose bound admits only a primitive, which
  // is never a thenable JavaScript would adopt instead. Without a value, the
  // promise settles to `undefined`, as an async function's completion.
  { global: "Promise", member: "resolve", signature: "resolve<T>(value: T): Promise<Awaited<T>>;",
    intrinsic: asyncReturnName },
  { global: "Promise", member: "resolve", signature: "resolve(): Promise<void>;", intrinsic: asyncCompleteName },
  // `%PromiseAll%`: an array of promises, each settling to its type
  // argument as `%Await%` assumes, gives a promise of the array of their
  // values. The declaration's parameter, values of any kind each adopted, is
  // stated as an array of promises.
  { global: "Promise", member: "all",
    signature: "all<T extends readonly unknown[] | []>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]>; }>;",
    intrinsic: promiseAllName },
];

/** The entry for `global`'s `member` (absent: its call) declared as `text`. */
export function globalEntry(entries: readonly GlobalEntry[], global: string, member: string | undefined,
    text: string): GlobalEntry | undefined {
  return entries.find(e => e.global === global && e.member === member && e.signature === text);
}
