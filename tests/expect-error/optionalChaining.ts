// @skjs-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const obj: { f: number } = { f: 1 };

// @skjs-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const obj2: { f?: number } = {};

function returningVoid(): void {}

function maybeObj(): { f: number } | undefined {
  return undefined;
}
function maybeObj2(): { f?: number } | null {
  return {};
}

// @skjs-expect-warning This '?.' is unnecessary; the value is never nullish, so use '.' instead
const x1: number = obj?.f;

// @skjs-expect-warning This '?.' is unnecessary; the value is never nullish, so use '.' instead
const x2: number | undefined = obj2?.f;

// @skjs-expect-warning The result of this optional chain is always 'undefined'
const x3: undefined = undefined?.f;

// @skjs-expect-warning The result of this optional chain is always 'undefined'
const x4: undefined = null?.f;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x5: null = maybeObj()?.f;

// @skjs-expect-error Property access is not allowed on this type
const x6: undefined = returningVoid()?.f;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x7: undefined = maybeObj()?.f;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x8: number = maybeObj()?.f;

const x9: number | undefined = maybeObj()?.f;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x10: undefined = maybeObj2()?.f;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const x11: number = maybeObj2()?.f;

const x12: number | undefined = maybeObj2()?.f;

// @ts-expect-error Unbound field: g
const x13: number | undefined = obj?.g;
