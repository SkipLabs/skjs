// Tests for distinguishing the `object` keyword type from `{}` (issue #674).
//
// Under SKJS's approach 4 (literal, distinct):
// - `{}` denotes any non-nullish value (primitives + non-primitive objects).
// - `object` denotes non-primitive values only (excludes primitives, null,
//   undefined, void, and `{}`).
// - Boxing remains off (`string </: { readonly length: number }`), so every
//   member-bearing structural object type, function, array, class instance,
//   and object literal is a subtype of `object`.
//
// Each function tests a single case so SKJS's one-error-per-def rule exercises
// every case independently.

///////////////////////////////////////////////////////////////////////////////
// 1. Primitives vs `{}` and `object`
///////////////////////////////////////////////////////////////////////////////

function stringToEmpty(): {} {
  return "hello";
}

function numberToEmpty(): {} {
  return 42;
}

function booleanToEmpty(): {} {
  return true;
}

function bigintToEmpty(): {} {
  return 1n;
}

function symbolToEmpty(): {} {
  return Symbol("s");
}

function nullToEmpty(): {} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return null;
}

function undefinedToEmpty(): {} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return undefined;
}

function voidToEmpty(u: void): {} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return u;
}

function stringToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hello";
}

function numberToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

function booleanToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return true;
}

function bigintToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 1n;
}

function symbolToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return Symbol("s");
}

function nullToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return null;
}

function undefinedToObject(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return undefined;
}

function primUnionToEmpty(x: string | number | boolean | bigint | symbol): {} {
  return x;
}

function primUnionToObject(
  x: string | number | boolean | bigint | symbol,
): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// 2. Relationship between `object` and `{}`
///////////////////////////////////////////////////////////////////////////////

function objectToEmpty(o: object): {} {
  return o;
}

// Rejected for soundness: `{}` admits primitives, so allowing `{}` into
// `object` would break transitivity (`string <: {} <: object`). Stricter than
// tsc, which unsoundly allows `{}` -> `object`.
function emptyToObject(e: {}): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return e;
}

interface EmptyInterface {}
class EmptyClass {}

function emptyInterfaceToEmpty(x: EmptyInterface): {} {
  return x;
}

function primToEmptyInterface(): EmptyInterface {
  return "hello";
}

// Empty structural interface is equivalent to `{}`: cannot flow into `object`.
function emptyInterfaceToObject(x: EmptyInterface): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Nominal class (even with no members) is always a non-primitive object.
function emptyClassToObject(x: EmptyClass): object {
  return x;
}

function primToEmptyClass(): EmptyClass {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hello";
}

///////////////////////////////////////////////////////////////////////////////
// 3. Genuine non-primitives and member-bearing shapes are subtypes of `object`
///////////////////////////////////////////////////////////////////////////////

function nonPrimitivesToObject(
  fn: () => void,
  fnType: Function,
  arr: number[],
  roArr: readonly number[],
  tup: [number, string],
  shape: { a: number },
  optShape: { a?: number },
  lenShape: { readonly length: number },
  idxShape: { [k: string]: number },
  closedEmpty: Closed<{}>,
): void {
  const o1: object = {};
  const lit = {};
  const o2: object = lit;
  const o3: object = {} as const;
  const o4: object = fn;
  const o5: object = fnType;
  const o6: object = arr;
  const o7: object = roArr;
  const o8: object = tup;
  const o9: object = shape;
  const o10: object = optShape;
  const o11: object = lenShape;
  const o12: object = idxShape;
  const o13: object = closedEmpty;
}

// Boxing stays off: primitives do NOT satisfy member-bearing shapes.
function stringToLengthShape(): { readonly length: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "hello";
}

function numberToFixedShape(): { toFixed(digits?: number): string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}

///////////////////////////////////////////////////////////////////////////////
// 4. Printing `object` vs `{}` in diagnostics
///////////////////////////////////////////////////////////////////////////////

function printObjectInError(): object {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line3 is not assignable to type 'object'
  return "hello";
}

function printEmptyInError(): {} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line3 is not assignable to type '{}'
  return null;
}

///////////////////////////////////////////////////////////////////////////////
// 5. Intersections with `object` and `{}`
///////////////////////////////////////////////////////////////////////////////

function interStringWithObject(x: string & object): never {
  return x;
}

function interNumberWithObject(x: number & object): never {
  return x;
}

function interStringWithEmpty(x: string & {}): string {
  return x;
}

function interNullableWithEmpty(x: (string | null | undefined) & {}): string {
  return x;
}

function interNullableWithEmptyNotNever(
  x: (string | null | undefined) & {},
): never {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function interPrimUnionWithObject(x: (string | { a: number }) & object): {
  a: number;
} {
  return x;
}

function interObjectAndEmpty(x: object & {}): object {
  return x;
}

function interEmptyAndObject(x: {} & object): object {
  return x;
}

function interStringAndNumberWithObject(x: (string | number) & object): never {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// 6. Equality overlap warnings and narrowing
///////////////////////////////////////////////////////////////////////////////

function eqObjectAndString(o: object, s: string): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return o === s;
}

function eqEmptyAndString(e: {}, s: string): boolean {
  return e === s;
}

function narrowEqEmptyAndString(e: {}, s: string): string {
  if (e === s) {
    return e;
  }
  return "";
}

function narrowEqObjectAndString(o: object, s: string): never {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  if (o === s) {
    return o;
  }
  throw new Error("unreachable");
}

///////////////////////////////////////////////////////////////////////////////
// 7. `typeof` narrowing on `{}` vs `object` vs `unknown`
///////////////////////////////////////////////////////////////////////////////

function typeofUnknownObjectToObject(u: unknown): object | null {
  if (typeof u === "object") {
    return u;
  }
  return null;
}

function typeofEmptyString(e: {}): string {
  if (typeof e === "string") {
    return e;
  }
  return "";
}

function typeofEmptyStringNotNever(e: {}): void {
  if (typeof e === "string") {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = e;
  }
}

function typeofObjectString(o: object): void {
  if (typeof o === "string") {
    const n: never = o;
  }
}

function typeofEmptyNumberNotNever(e: {}): void {
  if (typeof e === "number") {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = e;
  }
}

function typeofEmptyUndefined(e: {}): void {
  if (typeof e === "undefined") {
    const n: never = e;
  }
}

function typeofEmptyObject(e: {}): object | null {
  if (typeof e === "object") {
    return e;
  }
  return null;
}

function typeofObjectThenFunction(o: object): void {
  if (typeof o === "object") {
  } else if (typeof o === "function") {
  } else {
    const n: never = o;
  }
}

function typeofObjectFuncThenObj(o: object): void {
  if (typeof o === "function") {
  } else if (typeof o === "object") {
  } else {
    const n: never = o;
  }
}

function typeofEmptyObjectThenFunc(e: {}): void {
  if (typeof e === "object") {
  } else if (typeof e === "function") {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = e;
  }
}

function typeofEmptyFuncThenObj(e: {}): void {
  if (typeof e === "function") {
  } else if (typeof e === "object") {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = e;
  }
}

///////////////////////////////////////////////////////////////////////////////
// 8. Truthiness on `{}` vs `object`
///////////////////////////////////////////////////////////////////////////////

function truthyEmpty(e: {}): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (e) {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = e;
  }
}

function truthyObject(o: object): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (o) {
  } else {
    const n: never = o;
  }
}

///////////////////////////////////////////////////////////////////////////////
// 9. `in` operator, `Object.keys`, and generics
///////////////////////////////////////////////////////////////////////////////

function inOperatorOnObject(o: object): boolean {
  return "a" in o;
}

function inOperatorOnEmptyLiteral(): boolean {
  return "a" in {};
}

// `"a" in e` where `e: {}` throws TypeError at runtime when `e` is a primitive.
// Stricter than tsc, which unsoundly allows `in` on `{}`.
function inOperatorOnEmpty(e: {}): boolean {
  // @skjs-expect-error The right-hand side of an 'in' expression must be an object
  return "a" in e;
}

function objectKeysOnObject(o: object): string[] {
  return Object.keys(o);
}

function objectKeysOnEmptyLiteral(): string[] {
  return Object.keys({});
}

function objectKeysOnEmpty(e: {}): string[] {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return Object.keys(e);
}

function genericExtendsObject<T extends object>(x: T): object {
  return x;
}

function genericExtendsEmpty<T extends {}>(x: T): {} {
  return x;
}

function callGenericExtendsObjectValid(): void {
  const _a = genericExtendsObject({ a: 1 });
  const _b = genericExtendsObject({});
}

function callGenericExtendsObjectPrim(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const _a = genericExtendsObject("hello");
}

function callGenericExtendsEmptyValid(): void {
  const _a = genericExtendsEmpty({ a: 1 });
  const _b = genericExtendsEmpty({});
}

function callGenericExtendsEmptyPrim(): void {
  const _a = genericExtendsEmpty("hello");
}

function callGenericExtendsEmptyNull(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const _a = genericExtendsEmpty(null);
}
