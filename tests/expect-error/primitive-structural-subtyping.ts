// A primitive is a subtype of a structural object type whose members it has,
// via its wrapper class (a string has String.prototype, including `length`).
// Subtyping otherwise matches union members by tag and never relates a primitive
// to an object, so this bridge is what makes it work.

function wantsLength(x: { length: number }): number {
  return x.length;
}

// `string` has `length`, so it satisfies `{ length: number }`.
export function stringHasLength(): number {
  return wantsLength("hello");
}

// `number` has no `length`.
export function numberLacksLength(): number {
  // @ts-expect-error Argument is not assignable to the parameter's type
  return wantsLength(42);
}

// The bare `object` type means "non-primitive", so a primitive is not assignable
// to it (matching TypeScript).
function wantsObject(x: object): void {}
export function stringIsNotObject(): void {
  // @ts-expect-error Argument is not assignable to the parameter's type
  wantsObject("hello");
}

// skjs also does not treat a primitive as a subtype of `{}` (it represents `{}`
// and `object` identically); TypeScript accepts `string <: {}`. This is a known
// incompleteness.
function wantsEmpty(x: {}): void {}
export function stringIsNotEmptyObject(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  wantsEmpty("hello");
}
