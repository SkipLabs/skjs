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
 *   so a signature promising a result there would be false.
 *
 * A global declared outside the standard library, such as Node's `process`,
 * is read as its declaration states, member by member (`selectGlobal`). */
import type { TypeTerm } from "./declaration-types.mts";

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
};

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
  // `String(v)` converts a primitive, a symbol included, without running
  // client code; an object's conversion calls its `toString` or `valueOf`,
  // which may throw or return an object, and then `String` throws.
  // A test of the array's identity, which the calculus makes itself
  // (`Tag.isArray`): true of exactly the objects that own an array store,
  // JavaScript's Array exotic objects. The declared guard, `arg is any[]`,
  // is not read: Lean narrows by the clauses of the tested value's type.
  { global: "Array", member: "isArray", signature: "isArray(arg: any): arg is any[];", test: "isArray" },
  { global: "String", signature: "(value?: any): string;",
    admit: { parameter: "value", safe: ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"],
      literal: () => false } },
];

/** The entry for `global`'s `member` (absent: its call) declared as `text`. */
export function globalEntry(entries: readonly GlobalEntry[], global: string, member: string | undefined,
    text: string): GlobalEntry | undefined {
  return entries.find(e => e.global === global && e.member === member && e.signature === text);
}
