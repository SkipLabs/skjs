// Tests that rest parameters are implicitly readonly.
// ...x: T[] is treated as ...x: readonly T[] (ReadonlyArray<T>).

///////////////////////////////////////////////////////////////////////////////
// Rest param is ReadonlyArray, not Array
///////////////////////////////////////////////////////////////////////////////

function acceptsRO(...nums: number[]): ReadonlyArray<number> {
  return nums;
}

function rejectsArray(...nums: number[]): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const arr: Array<number> = nums;
}

///////////////////////////////////////////////////////////////////////////////
// Element read works, mutation does not
///////////////////////////////////////////////////////////////////////////////

function readElement(...items: string[]): string | undefined {
  return items[0];
}

function noMutation(...items: string[]): void {
  // @ts-expect-error Invalid index key: expected number, got string
  items.push("x");
}

///////////////////////////////////////////////////////////////////////////////
// Explicit readonly T[] annotation still works
///////////////////////////////////////////////////////////////////////////////

function explicitReadonly(...x: readonly number[]): ReadonlyArray<number> {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Function type annotations: rest params in function types are also readonly
///////////////////////////////////////////////////////////////////////////////

type RestFn = (...args: number[]) => void;

function takesRestFn(f: RestFn): void {
  f(1, 2, 3);
}

///////////////////////////////////////////////////////////////////////////////
// Subtyping: function with rest is assignable to compatible type
///////////////////////////////////////////////////////////////////////////////

function implRest(_a: number, ..._rest: string[]): void {}
function testSubtyping(): void {
  const f: (a: number, ...rest: string[]) => void = implRest;
}

///////////////////////////////////////////////////////////////////////////////
// Tuple rest params
// Tuples are already non-assignable to mutable Array, but index mutation
// is not yet rejected (requires readonly tuple support).
///////////////////////////////////////////////////////////////////////////////

// FIXME: tuple rest should reject index mutation, but readonly tuples aren't supported yet
function tupleMutation(...args: [string, number]): void {
  args[0] = "x";
}

// Tuple rest is already not assignable to mutable Array
function tupleToArray(...args: [string, number]): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const arr: Array<string | number> = args;
}

///////////////////////////////////////////////////////////////////////////////
// Generic rest type variable is readonly inside the body
///////////////////////////////////////////////////////////////////////////////

function genericRestMutation<T extends ReadonlyArray<number>>(
  ...args: T
): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const arr: Array<number> = args;
}

///////////////////////////////////////////////////////////////////////////////
// Type alias: rest param with type alias for array is also readonly
///////////////////////////////////////////////////////////////////////////////

type Numbers = number[];

// FIXME: type alias rest should also be treated as readonly, but
// arrayToReadonlyArray only matches literal Array<T>, not aliases.
// Compare with acceptsRO/rejectsArray above which use `number[]` directly.

// This works because nums stays as Array<number> (not converted to readonly),
// and Array<number> is assignable to ReadonlyArray<number>.
function aliasRest(...nums: Numbers): ReadonlyArray<number> {
  // FIXME: This mutation should be rejected but isn't,
  // because nums is still mutable Array<number>.
  nums.push(42);
  return nums;
}

// FIXME: This should error (like rejectsArray above) but doesn't,
// because the type alias prevents the Array→ReadonlyArray conversion.
function aliasRestRejectsArray(...nums: Numbers): void {
  const arr: Array<number> = nums;
}

// Non-alias version correctly rejects the same assignment.
function nonAliasRestRejectsArray(...nums: number[]): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const arr: Array<number> = nums;
}

///////////////////////////////////////////////////////////////////////////////
// Shared type parameter: T used for both rest param and mutable sink.
// Without readonly rest, the sink could mutate the rest array unsoundly.
///////////////////////////////////////////////////////////////////////////////

function passThroughToSink<T>(
  sink: (items: Array<T>) => void,
  ...items: T[]
): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  sink(items);
}

function passThroughToSinkRO<T>(
  sink: (items: ReadonlyArray<T>) => void,
  ...items: T[]
): void {
  sink(items);
}

function assignRestToMutable<T>(target: Array<T>, ...source: T[]): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const copy: Array<T> = source;
}

function assignRestToReadonly<T>(
  target: ReadonlyArray<T>,
  ...source: T[]
): void {
  const copy: ReadonlyArray<T> = source;
}

///////////////////////////////////////////////////////////////////////////////
// Full-array type parameter with mutable constraint:
// <T extends SomeType[]>(...rest: T) is rejected because mutable Array
// constraints are unsound for rest parameters.
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error A rest parameter's constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
function fullMutableConstraint<T extends string[]>(...args: T): void {
  // If this were allowed, T = string[] means args is mutable,
  // and a mutator could .push() on the rest array.
  const mutRef: T = args;
}

function fullMutableWithSink<T extends string[]>(
  mutator: (arr: T) => void,
  // @skjs-expect-error A rest parameter's constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
  ...args: T
): void {
  // If this were allowed, mutator could mutate the rest array.
  mutator(args);
}

// @skjs-expect-error A rest parameter's constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
function fullMutableReturn<T extends number[]>(...args: T): T {
  // If this were allowed, caller gets a mutable handle to the rest array.
  return args;
}

///////////////////////////////////////////////////////////////////////////////
// Full-array type parameter with readonly constraint:
// <T extends readonly SomeType[]>(...rest: T) is allowed, but args has type T
// which could still be a mutable subtype — needs Readonly<T>.
///////////////////////////////////////////////////////////////////////////////

// FIXME: args has type T which could be a mutable array type.
// Ideally args should be Readonly<T>, but Readonly<> isn't supported yet.
function fullReadonlyConstraint<T extends readonly string[]>(...args: T): void {
  // T could be string[] (mutable subtype of readonly string[]).
  // Currently args has type T, so this passes even though it shouldn't.
  const mutRef: T = args;
}

// FIXME: same soundness hole with a sink
function fullReadonlyWithSink<T extends readonly string[]>(
  mutator: (arr: T) => void,
  ...args: T
): void {
  // This passes because args: T and mutator expects T.
  // If T = string[], mutator could call .push() on the rest array.
  mutator(args);
}
