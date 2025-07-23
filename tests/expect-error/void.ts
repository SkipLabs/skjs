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
  // @ts-expect-error Invalid return type
  return undefined;
}

function returningVoid6(): void {
  return returningVoid();
}

function returningVoid7(): void {
  // @ts-expect-error Invalid return type
  return null;
}

const x: void = returningVoid();

// @ts-expect-error Invalid definition
const x2: void = undefined;

// @ts-expect-error Invalid definition
const x3: void = {};

// @ts-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const x4: () => void = () => null;

// @ts-expect-error Expected an array
const x5: undefined = returningVoid()["bla"];

// @ts-expect-error Invalid comparison. You can only compare strings, numbers, and booleans.
const x6: boolean = returningVoid() < returningVoid();

// @ts-expect-error Invalid operation on type void
const x7: boolean = returningVoid() === returningVoid();

type t = void | undefined; // We may want an error here (see #76)

// @ts-expect-error This function may not always return a value
function returningVoidOrNull(): void | null {}

// @ts-expect-error This function may not always return a value
function returningVoidOrNumber(): void | number {}

// @ts-expect-error This function may not always return a value
function returningVoidOrUndefined(): void | undefined {}

// @ts-expect-error Invalid '.'
const x8: string | undefined = returningVoid()?.toString();

// @ts-expect-error Invalid '.'
const x9: string | undefined = returningVoidOrNumber()?.toString();

// @ts-expect-error Invalid operation on type void
const x10: number | undefined = returningVoid() ?? 0;

// @ts-expect-error Invalid operation on type void
const x11: number | undefined = returningVoidOrNumber() ?? 0;

// @ts-expect-error Invalid operation on type void
const x12: number | undefined = returningVoidOrUndefined() ?? 0;

// @ts-expect-error Invalid operation on type void
const x13: number | void | null = returningVoidOrNull() ?? 0;

// @ts-expect-error Invalid ||
const x14: number | undefined = returningVoid() || 0;

// @ts-expect-error Invalid ||
const x15: number | undefined = returningVoidOrNumber() || 0;

// @ts-expect-error Invalid ||
const x16: number | undefined = returningVoidOrUndefined() || 0;

// @ts-expect-error Invalid ||
const x17: number | void | null = returningVoidOrNull() || 0;

function unsafeInTypescript(b: boolean, returningVoid: () => void): string {
  // @ts-expect-error Invalid operation on type void
  return (b ? null : returningVoid()) ?? "a";
}
// @ts-expect-error Invalid call
unsafeInTypescript(false, returningVoidOrNumber);

/* With type parameters */

// @ts-expect-error This function may not always return a value
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
  // @ts-expect-error Invalid operation on type void
  return value ?? null;
}

function invalidLogicalOr<T>(value: void | T): T {
  // @ts-expect-error Invalid ||
  return value || null;
}

function invalidPropertyAccess<T>(value: void | T): string {
  // @ts-expect-error Invalid '.' for type: void | T:T:10:3523836110
  return value.toString();
}

function invalidOptionalChaining<T>(value: void | T): string {
  // @ts-expect-error Invalid '.' for type: void | T:T:11:3523836110
  return value?.toString();
}

function invalidComparison<T>(value1: void | T, value2: void | T): boolean {
  // @ts-expect-error Invalid comparison. You can only compare strings, numbers, and booleans.
  return value1 < value2;
}

function invalidArrayAccess<T>(value: void | T): T {
  // @ts-expect-error Expected an array
  return value[0];
}

function invalidFunctionCall<T>(value: void | T): T {
  // @ts-expect-error Invalid call
  return value();
}

function validVoidUnionUsage<T>(value: void | T): boolean {
  // @ts-expect-error Invalid operation on type void
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

// @ts-expect-error Invalid operation on type void
const x18: boolean = typeof returningVoid() === "undefined";

// @ts-expect-error Invalid operation on type void
const x19: boolean = typeof returningVoidOrNull() === "undefined";

// @ts-expect-error Invalid operation on type void
const x20: boolean = returningVoid() === undefined;

// @ts-expect-error Invalid operation on type void
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
