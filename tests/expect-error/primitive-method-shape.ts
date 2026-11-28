// Primitive inhabitance of structural object & method shapes (#982).
//
// Non-nullish primitives (`string`, `number`, `boolean`, `bigint`, `symbol`,
// and their literal subtypes) inhabit structural object shapes whose members
// are satisfied by the primitive's boxed prototype (`declare class string`,
// `number`, `boolean`, `bigint`, `symbol` in import-stubs), while preserving
// full soundness:
// - `object`, `null`, `undefined`, `void`, nominal classes, arrays, callables,
//   `Closed<...>`, and mutable fields still reject primitives.
// - Method-syntax shape members (`{ m(): R }`) stay attach-only; extracting
//   or laundering them is rejected, and property-syntax free-function slots
//   (`{ readonly toFixed: () => string }`) reject `this`-requiring primitive
//   methods.
// - Because primitives inhabit primitive-compatible structural shapes
//   (e.g. `{ readonly length: number }`, `{ toUpperCase(): string }`), those
//   shapes cannot flow into `object`, reject `in`, may be falsy, and narrow
//   soundly under `typeof`.

///////////////////////////////////////////////////////////////////////////////
// 1. Positive: primitives & literals inhabit method-syntax and readonly shapes
///////////////////////////////////////////////////////////////////////////////

type HasToUpperCase = { toUpperCase(): string };
type HasToFixed = { toFixed(digits?: number): string };
type HasToString = { toString(): string };
type HasBigIntToString = { toString(radix?: number): string };
type HasReadonlyLength = { readonly length: number };
type HasValueOfNumber = { valueOf(): number };
type HasReadonlyToFixedWithThis = {
  readonly toFixed: (this: number, digits?: number) => string;
};
type StringArrayLike = {
  readonly length: number;
  readonly [index: number]: string | undefined;
};

function stringLitToMethodShape(): HasToUpperCase {
  return "hi";
}

function stringToMethodShape(s: string): HasToUpperCase {
  return s;
}

function numberLitToMethodShape(): HasToFixed {
  return 42;
}

function numberToMethodShape(n: number): HasToFixed {
  return n;
}

function numberToValueOf(): HasValueOfNumber {
  return 42;
}

function boolLitToToString(): HasToString {
  return true;
}

function boolToToString(b: boolean): HasToString {
  return b;
}

// `bigint.toString(radix?: number)` accepts an optional parameter; SKJS
// rejects assigning a function with extra optional parameters to a 0-arity
// target (`() => string`), so `bigint` inhabits `{ toString(radix?: number): string }`
// (and `{ valueOf(): bigint }`), while `{ toString(): string }` stays rejected.
function bigintLitToToString(): HasToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 1n;
}

function bigintToToString(bi: bigint): HasToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return bi;
}

function bigintLitToBigIntToString(): HasBigIntToString {
  return 1n;
}

function bigintToBigIntToString(bi: bigint): HasBigIntToString {
  return bi;
}

function bigintToValueOf(bi: bigint): { valueOf(): bigint } {
  return bi;
}

function symbolToToString(sym: symbol): HasToString {
  return sym;
}

function stringToReadonlyLength(s: string): HasReadonlyLength {
  return s;
}

function stringLitToReadonlyLength(): HasReadonlyLength {
  return "hi";
}

function stringToArrayLike(s: string): StringArrayLike {
  return s;
}

// Property-syntax `{ readonly toFixed: (this: number, ...) => string }`
// requires an own enumerable property (not omitted by object spread); prototype
// methods are non-enumerable (`mayBeOmittedByCopy`), so only method-syntax
// `{ toFixed(digits?: number): string }` accepts them (same as class methods).
function numberToReadonlyExplicitThis(): HasReadonlyToFixedWithThis {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

function primUnionToToString(x: string | number | boolean): HasToString {
  return x;
}

function stringToUnionShape(
  s: string,
): HasToUpperCase | { readonly a: number } {
  return s;
}

function optionalPrototypeMethod(): { toFixed?(digits?: number): string } {
  return 42;
}

// Generic constraint satisfied by primitives.
function formatFixed<T extends HasToFixed>(x: T): string {
  return x.toFixed(2);
}

function callGenericWithNumberLit(): string {
  return formatFixed(42);
}

function callGenericWithNumber(n: number): string {
  return formatFixed(n);
}

function genericToUpper<T extends HasToUpperCase>(x: T): string {
  return x.toUpperCase();
}

function callGenericWithString(): string {
  return genericToUpper("hello");
}

///////////////////////////////////////////////////////////////////////////////
// 2. Negative: nullish, wrong prototype, mutable, free-call, nominal, Closed
///////////////////////////////////////////////////////////////////////////////

function nullToMethodShape(): HasToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return null;
}

function undefinedToMethodShape(): HasToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return undefined;
}

function voidToMethodShape(v: void): HasToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return v;
}

function nullableStringToMethodShape(s: string | null): HasToUpperCase {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

function stringToNumberMethod(): HasToFixed {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

function numberToStringMethod(): HasToUpperCase {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

function numberToLengthShape(): HasReadonlyLength {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

// Mutable fields on primitive prototypes MUST be rejected.
function stringToMutableLength(): { length: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

function stringToMutableIndex(): { [index: number]: string | undefined } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

function directMutateStringLength(s: string): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  s.length = 5;
}

function directMutateStringIndex(s: string): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  s[0] = "a";
}

function numberToMutableMethodProp(): {
  toFixed: (this: number, digits?: number) => string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

// Property-syntax free function rejects `this`-requiring primitive methods (#960).
function numberToFreeFunctionProp(): { readonly toFixed: () => string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

function stringToFreeFunctionProp(): { readonly toUpperCase: () => string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

// Non-primitive intersection (`& object`) rejects primitives (#674).
function stringToNonPrimitiveMethodShape(): HasToUpperCase & object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

function numberToNonPrimitiveMethodShape(): HasToFixed & object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

// Closed<...> rejects primitives.
function numberToClosedMethodShape(): Closed<HasToFixed> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

function stringToClosedLengthShape(): Closed<HasReadonlyLength> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

// Nominal class with matching method rejects primitives (#1062).
class NominalToString {
  toString(): string {
    return "x";
  }
}

function stringToNominalClass(): NominalToString {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

// Array / ReadonlyArray rejects string even though string has length & [number].
function stringToReadonlyArray(): readonly (string | undefined)[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

// Callable shape rejects primitives.
function stringToCallable(): (() => string) & HasToUpperCase {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hi";
}

// Extracting / laundering a shape method after boxing stays rejected (#960 / #1020).
function detachAfterBoxing(): string {
  const s: HasToUpperCase = "hi";
  const f = s.toUpperCase;
  // @skjs-expect-error A shape method can only be called on the object it was accessed on
  return f();
}

function reattachAfterBoxing(): HasToUpperCase {
  const s: HasToUpperCase = "hi";
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { toUpperCase: s.toUpperCase };
}

// Spreading a primitive-inhabited shape cannot assume non-enumerable fields
// (like `"hi".length`) survived the spread.
function spreadLengthShape(x: HasReadonlyLength): { readonly length: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}

///////////////////////////////////////////////////////////////////////////////
// 3. Soundness invariants: primitive-inhabited shapes vs `object`, `in`,
//    `typeof`, truthiness, and intersections
///////////////////////////////////////////////////////////////////////////////

// A shape inhabited by primitives must NOT flow into `object` (otherwise
// `"hi" <: { toUpperCase(): string } <: object` breaks transitivity).
function methodShapeToObject(x: HasToUpperCase): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function lengthShapeToObject(x: HasReadonlyLength): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A non-primitive intersection `{ toUpperCase(): string } & object` IS `object`.
function nonPrimMethodShapeToObject(x: HasToUpperCase & object): object {
  return x;
}

// A shape with a field not on any primitive stays provably non-primitive.
function nonPrimReadonlyShapeToObject(x: { readonly custom: number }): object {
  return x;
}

// `in` throws TypeError on primitives, so primitive-inhabited shapes reject `in`.
function inOnMethodShape(x: HasToUpperCase): boolean {
  // @skjs-expect-error The right-hand side of an 'in' expression must be an object
  return "toUpperCase" in x;
}

function inOnLengthShape(x: HasReadonlyLength): boolean {
  // @skjs-expect-error The right-hand side of an 'in' expression must be an object
  return "length" in x;
}

function inOnNonPrimReadonlyShape(x: { readonly custom: number }): boolean {
  // @skjs-expect-warning This condition is always true
  return "custom" in x;
}

function inOnNonPrimMethodShape(x: HasToUpperCase & object): boolean {
  // @skjs-expect-warning This condition is always true
  return "toUpperCase" in x;
}

// `typeof` narrowing: primitive-inhabited shapes narrow to matching primitives
// and drop to `never` for non-matching primitives.
function typeofLengthIsString(x: HasReadonlyLength): string {
  if (typeof x === "string") {
    return x;
  }
  return "";
}

function typeofLengthIsStringNotNever(x: HasReadonlyLength): void {
  if (typeof x === "string") {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

function typeofLengthIsNumberIsNever(x: HasReadonlyLength): void {
  if (typeof x === "number") {
    const n: never = x;
  }
}

function typeofToFixedIsNumberNotNever(x: HasToFixed): void {
  if (typeof x === "number") {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

function typeofToFixedIsStringIsNever(x: HasToFixed): void {
  if (typeof x === "string") {
    const n: never = x;
  }
}

function typeofLengthObjectThenFunctionNotNever(x: HasReadonlyLength): void {
  if (typeof x === "object") {
  } else if (typeof x === "function") {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

function typeofLengthFuncThenObjNotNever(x: HasReadonlyLength): void {
  if (typeof x === "function") {
  } else if (typeof x === "object") {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

// Truthiness: `""` inhabits `HasReadonlyLength` and `HasToUpperCase`, and `0`
// inhabits `HasToFixed`, so the else branch is reachable (not `never`).
function truthyLengthElseNotNever(x: HasReadonlyLength): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

function truthyToFixedElseNotNever(x: HasToFixed): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

function truthyNonPrimReadonlyElseIsNever(x: {
  readonly custom: number;
}): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
  } else {
    const n: never = x;
  }
}

// Intersections with unions of primitives.
function interNullableStringWithMethodShape(
  x: (string | null) & HasToUpperCase,
): string {
  return x;
}

function interPrimUnionWithToFixed(x: (string | number) & HasToFixed): number {
  return x;
}

function interStringWithMethodShapeNotNever(x: string & HasToUpperCase): never {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function interStringWithWrongMethodShape(x: string & HasToFixed): never {
  return x;
}
