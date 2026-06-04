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

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @skjs-expect-error The type of a top-level constant must be a primitive type, not an object
const x4: () => void = () => null;

// @skjs-expect-error Property access is not allowed on this type
const x5: undefined = returningVoid()["bla"];

// @skjs-expect-error A comparison operand must be a string, number, bigint, or boolean
const x6: boolean = returningVoid() < returningVoid();

// @skjs-expect-error An expression of type 'void' cannot be used here
const x7: boolean = returningVoid() === returningVoid();

type t = void | undefined; // We may want an error here (see #76)

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function returningVoidOrNull(): void | null {}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function returningVoidOrNumber(): void | number {}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function returningVoidOrUndefined(): void | undefined {}

// @skjs-expect-error Property access is not allowed on this type
const x8: string | undefined = returningVoid()?.toString();

// @skjs-expect-error Property access is not allowed on this type
const x9: string | undefined = returningVoidOrNumber()?.toString();

// @skjs-expect-error An expression of type 'void' cannot be used here
const x10: number | void = returningVoid() ?? 0;

// @skjs-expect-error An expression of type 'void' cannot be used here
const x11: number | void = returningVoidOrNumber() ?? 0;

// @skjs-expect-error An expression of type 'void' cannot be used here
const x12: number | void = returningVoidOrUndefined() ?? 0;

// @skjs-expect-error An expression of type 'void' cannot be used here
const x13: number | void | null = returningVoidOrNull() ?? 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @skjs-expect-error Operand of '||' must be of type 'boolean'
const x14: number | undefined = returningVoid() || 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @skjs-expect-error Operand of '||' must be of type 'boolean'
const x15: number | undefined = returningVoidOrNumber() || 0;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
// @skjs-expect-error Operand of '||' must be of type 'boolean'
const x16: number | undefined = returningVoidOrUndefined() || 0;

// @skjs-expect-error Operand of '||' must be of type 'boolean'
const x17: number | void | null = returningVoidOrNull() || 0;

function unsafeInTypescript(
  b: boolean,
  returningVoid: () => void,
): string | void {
  // @skjs-expect-error An expression of type 'void' cannot be used here
  return (b ? null : returningVoid()) ?? "a";
}
// @skjs-expect-error Argument is not assignable to the parameter's type
// @skjs-expect-error This expression was expected to be of type 'void'
unsafeInTypescript(false, returningVoidOrNumber);

/* With type parameters */

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function returningGenericVoid<T>(): T | void {}

function returningConstrainedVoid<T extends void>(): T {}

function returningVoidParam<T extends void>(param: T): void {
  return param;
}

function takesVoidGeneric<T extends void>(param: T): void {}

// @skjs-expect-error Argument is not assignable to the parameter's type
takesVoidGeneric<number>(5);

takesVoidGeneric<void>(returningVoid());

function callGenericVoidFunction<T>(arg: T): void {
  const func = (x: T) => {};
  return func(arg);
}

const result: void = callGenericVoidFunction("test");

type VoidOrT<T> = void | T;

function invalidNullishCoalescing<T>(value: void | T): void | T | null {
  // @skjs-expect-error An expression of type 'void' cannot be used here
  return value ?? null;
}

function invalidLogicalOr<T>(value: void | T): T {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error Operand of '||' must be of type 'boolean'
  return value || null;
}

function invalidPropertyAccess<T>(value: void | T): string {
  // @skjs-expect-error Cannot access a property on type void | T:10:828896147511048019
  return value.toString();
}

function invalidOptionalChaining<T>(value: void | T): string {
  // @skjs-expect-error Cannot access a property on type void | T:11:828896147511048019
  return value?.toString();
}

function invalidComparison<T>(value1: void | T, value2: void | T): boolean {
  // @skjs-expect-error A comparison operand must be a string, number, bigint, or boolean
  return value1 < value2;
}

function invalidArrayAccess<T>(value: void | T): T {
  // @skjs-expect-error Cannot access a property on type void | T:13:828896147511048019
  return value[0];
}

function invalidFunctionCall<T>(value: void | T): T {
  // @skjs-expect-error This expression is not callable
  return value();
}

function validVoidUnionUsage<T>(value: void | T): boolean {
  // @skjs-expect-error An expression of type 'void' cannot be used here
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

// @skjs-expect-error An expression of type 'void' cannot be used here
const x18: boolean = typeof returningVoid() === "undefined";

// @skjs-expect-error An expression of type 'void' cannot be used here
const x19: boolean = typeof returningVoidOrNull() === "undefined";

// @skjs-expect-error An expression of type 'void' cannot be used here
const x20: boolean = returningVoid() === undefined;

// @skjs-expect-error An expression of type 'void' cannot be used here
const x21: boolean = returningVoidOrNull() === null;

// @skjs-expect-error Operator '+' cannot be applied to these types
const x22: number = returningVoid() + 5;

// @skjs-expect-error This operator requires a numeric operand
const x23: number = returningVoid() - 5;

// @skjs-expect-error This operator requires a numeric operand
const x24: number = returningVoid() * 5;

// @skjs-expect-error This operator requires a numeric operand
const x25: number = returningVoid() / 5;

// @skjs-expect-error This operator requires a numeric operand
const x26: number = returningVoid() % 5;

// Additional operations that should be disallowed on void

function testConditionalWithVoid(): number {
  // @skjs-expect-error A ternary condition must be of type 'boolean'
  return returningVoid() ? 1 : 0;
}

function testArithmeticAssignment(): void {
  let x: number = 5;
  // @skjs-expect-error Right operand of '+' is not assignable to the left operand's type
  x += returningVoid();
}
