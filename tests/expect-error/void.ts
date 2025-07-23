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

// TODO: change to forbidden on void
// @ts-expect-error This operator is useless
const x10: number | undefined = returningVoid() ?? 0;

// TODO: change to forbidden on void
// @ts-expect-error This operator is useless
const x11: number | undefined = returningVoidOrNumber() ?? 0;

// TODO: change to forbidden on void
// @ts-expect-error Invalid definition
const x12: number | undefined = returningVoidOrUndefined() ?? 0;

// TODO: change to forbidden on void
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
  // @ts-expect-error Invalid return type
  return (b ? null : returningVoid()) ?? "a";
}
// @ts-expect-error Invalid call
unsafeInTypescript(false, returningVoidOrNumber);
