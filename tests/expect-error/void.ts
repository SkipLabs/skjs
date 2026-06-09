function returningVoid(): void {}

function returningVoid2(): void {
  return;
}

function returningVoid3(): void {
  while (true) {}
}

function returningVoid4(): void {
  throw {};
}

function returningVoid5(): void {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return undefined;
}

function returningVoid6(): void {
  return returningVoid();
}

function returningVoid7(): void {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return null;
}

const x: void = returningVoid();

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x2: void = undefined;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x3: void = {};

// @skjs-expect-error Invalid type for constant, only primitive types (not objects) are allowed
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x4: () => void = () => null;

// @skjs-expect-error Type cannot be accessed
const x5: undefined = returningVoid()["bla"];

// @skjs-expect-error Invalid comparison. You can only compare strings, numbers, bigints, and booleans.
const x6: boolean = returningVoid() < returningVoid();

// @skjs-expect-error Invalid operation on type void
const x7: boolean = returningVoid() === returningVoid();

type t = void | undefined; // We may want an error here (see #76)

// @skjs-expect-error This function may not always return a value
function returningVoidOrNull(): void | null {}

// @skjs-expect-error This function may not always return a value
function returningVoidOrNumber(): void | number {}

// @skjs-expect-error This function may not always return a value
function returningVoidOrUndefined(): void | undefined {}

// @ts-expect-error Type cannot be accessed
const x8: string | undefined = returningVoid()?.toString();

// @ts-expect-error Type cannot be accessed
const x9: string | undefined = returningVoidOrNumber()?.toString();

// @skjs-expect-error Invalid operation on type void
const x10: number | void = returningVoid() ?? 0;

// @skjs-expect-error Invalid operation on type void
const x11: number | void = returningVoidOrNumber() ?? 0;

// @skjs-expect-error Invalid operation on type void
const x12: number | void = returningVoidOrUndefined() ?? 0;

// @skjs-expect-error Invalid operation on type void
const x13: number | void | null = returningVoidOrNull() ?? 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @ts-expect-error Invalid ||
const x14: number | undefined = returningVoid() || 0;

// @skjs-expect-error Invalid ||
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x15: number | undefined = returningVoidOrNumber() || 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @ts-expect-error Invalid ||
const x16: number | undefined = returningVoidOrUndefined() || 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @ts-expect-error Invalid ||
const x17: number | void | null = returningVoidOrNull() || 0;

function unsafeInTypescript(
  b: boolean,
  returningVoid: () => void,
): string | void {
  // @skjs-expect-error Invalid operation on type void
  return (b ? null : returningVoid()) ?? "a";
}
// @skjs-expect-error Invalid call
// @skjs-expect-error This expression was expected to be of type void
unsafeInTypescript(false, returningVoidOrNumber);

/* With type parameters */

// @skjs-expect-error This function may not always return a value
function returningGenericVoid<T>(): T | void {}

function returningConstrainedVoid<T extends void>(): T {}

function returningVoidParam<T extends void>(param: T): void {
  return param;
}

function takesVoidGeneric<T extends void>(param: T): void {}

// @ts-expect-error Invalid call
takesVoidGeneric<number>(5);

takesVoidGeneric<void>(returningVoid());

function callGenericVoidFunction<T>(arg: T): void {
  const func = (x: T) => {};
  return func(arg);
}

const result: void = callGenericVoidFunction("test");

type VoidOrT<T> = void | T;

function invalidNullishCoalescing<T>(value: void | T): void | T | null {
  // @skjs-expect-error Invalid operation on type void
  return value ?? null;
}

function invalidLogicalOr<T>(value: void | T): T {
  // @skjs-expect-error Invalid ||
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return value || null;
}

function invalidPropertyAccess<T>(value: void | T): string {
  // @ts-expect-error Invalid access for type void | T:10:828896147511048019
  return value.toString();
}

function invalidOptionalChaining<T>(value: void | T): string {
  // @ts-expect-error Invalid access for type void | T:11:828896147511048019
  return value?.toString();
}

function invalidComparison<T>(value1: void | T, value2: void | T): boolean {
  // @skjs-expect-error Invalid comparison. You can only compare strings, numbers, bigints, and booleans.
  return value1 < value2;
}

function invalidArrayAccess<T>(value: void | T): T {
  // @ts-expect-error Invalid access for type void | T:13:828896147511048019
  return value[0];
}

function invalidFunctionCall<T>(value: void | T): T {
  // @ts-expect-error Invalid call
  return value();
}

function validVoidUnionUsage<T>(value: void | T): boolean {
  // @skjs-expect-error Invalid operation on type void
  return value === value;
}

function conditionalVoidUnion<T>(condition: boolean, fallback: T): void | T {
  if (condition) {
    return;
  }
  return fallback;
}

interface VoidGenericInterface<T> {
  method(): T | void;
}

class VoidGenericClass<T> implements VoidGenericInterface<T> {
  method(): T | void {
    return;
  }
}

// @skjs-expect-error Invalid operation on type void
const x18: boolean = typeof returningVoid() === "undefined";

// @skjs-expect-error Invalid operation on type void
const x19: boolean = typeof returningVoidOrNull() === "undefined";

// @skjs-expect-error Invalid operation on type void
const x20: boolean = returningVoid() === undefined;

// @skjs-expect-error Invalid operation on type void
const x21: boolean = returningVoidOrNull() === null;

// @ts-expect-error Invalid + operation
const x22: number = returningVoid() + 5;

// @ts-expect-error Invalid operation
const x23: number = returningVoid() - 5;

// @ts-expect-error Invalid operation
const x24: number = returningVoid() * 5;

// @ts-expect-error Invalid operation
const x25: number = returningVoid() / 5;

// @ts-expect-error Invalid operation
const x26: number = returningVoid() % 5;

// Additional operations that should be disallowed on void

function testConditionalWithVoid(): number {
  // @ts-expect-error Invalid ? condition
  return returningVoid() ? 1 : 0;
}

function testArithmeticAssignment(): void {
  let x: number = 5;
  // @ts-expect-error Invalid + operand
  x += returningVoid();
}
