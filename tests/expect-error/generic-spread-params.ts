// Tests for generic spread/rest parameters
//
// Standard pattern: ...args: T[] (element type extracted via Symbol.iterator)
// Bare TVar pattern: ...args: T where T extends ReadonlyArray<X>

///////////////////////////////////////////////////////////////////////////////
// Standard generic spread: ...args: T[]
///////////////////////////////////////////////////////////////////////////////

// Generic spread where all args go through spread
function collectAll<T>(...items: T[]): Array<T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return items;
}

function testCollectAll(): void {
  let a1 = collectAll(1, 2, 3);
  let a1check: Array<number> = a1;
}

// Fixed version: return ReadonlyArray since rest params are readonly
function collectAllRO<T>(...items: T[]): ReadonlyArray<T> {
  return items;
}

function testCollectAllRO(): void {
  let a1 = collectAllRO(1, 2, 3);
  let a1check: ReadonlyArray<number> = a1;
}

// Explicit param constrains T, extra args checked via spread
function pushAll<T>(first: T, ...rest: T[]): Array<T> {
  return [first, ...rest];
}

function testPushAll(): void {
  let b1 = pushAll(1, 2, 3);
  let b1check: Array<number> = b1;
}

// Return type uses T from spread
function combine<T>(first: T, ...rest: T[]): T {
  return first;
}

function testCombine(): void {
  let f1: number = combine(1, 2, 3);
}

///////////////////////////////////////////////////////////////////////////////
// Bare TVar spread: ...args: T where T extends ReadonlyArray<X>
///////////////////////////////////////////////////////////////////////////////

function bareSpread<T extends ReadonlyArray<number>>(
  ...args: T
): ReadonlyArray<number> {
  return args;
}

function testBareSpread(): void {
  let r = bareSpread(1, 2, 3);
}

function bareSpreadStr<T extends ReadonlyArray<string>>(...items: T): void {
  for (const s of items) {
    console.log(s);
  }
}

function testBareSpreadStr(): void {
  bareSpreadStr("a", "b", "c");
}

///////////////////////////////////////////////////////////////////////////////
// Bare TVar spread must reject mutable Array constraints
///////////////////////////////////////////////////////////////////////////////

// @ts-expect-error Rest parameter constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
function bareMutable<T extends Array<number>>(...args: T): void {}

// @ts-expect-error Rest parameter constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
function bareShorthand<T extends number[]>(...args: T): void {}

type MutableNums = number[];

// @ts-expect-error Rest parameter constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly
function aliasMutable<T extends MutableNums>(...args: T): void {}
