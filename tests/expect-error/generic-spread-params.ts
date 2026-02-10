// Tests for generic spread/rest parameters
//
// Standard pattern: ...args: T[] (element type extracted via Symbol.iterator)
// Bare TVar pattern: ...args: T where T extends Array<X> (not yet supported)

///////////////////////////////////////////////////////////////////////////////
// Standard generic spread: ...args: T[]
///////////////////////////////////////////////////////////////////////////////

// Generic spread where all args go through spread
function collectAll<T>(...items: T[]): Array<T> {
  return items;
}

function testCollectAll(): void {
  let a1 = collectAll(1, 2, 3);
  let a1check: Array<number> = a1;
}

// Explicit param constrains T, extra args checked via spread
function pushAll<T>(first: T, ...rest: T[]): Array<T> {
  return [first, ...rest];
}

function testPushAll(): void {
  let b1 = pushAll(1, 2, 3);
  let b1check: Array<number> = b1;
}

// Generic spread, return type should be precise
function identity<T>(...args: T[]): Array<T> {
  return args;
}

function testIdentitySpread(): void {
  let d1 = identity(1, 2, 3);
  let d1check: Array<number> = d1;
}

// Return type uses T from spread
function combine<T>(first: T, ...rest: T[]): T {
  return first;
}

function testCombine(): void {
  let f1: number = combine(1, 2, 3);
}

///////////////////////////////////////////////////////////////////////////////
// Bare TVar spread: ...args: T where T extends Array<X>
// TODO: not yet supported — element type extraction doesn't work for bare TVars
///////////////////////////////////////////////////////////////////////////////

function bareSpread<T extends Array<number>>(...args: T): Array<number> {
  return args;
}

function testBareSpread(): void {
  // @skjs-expect-error Invalid call. Unexpected type for ...
  let r = bareSpread(1, 2, 3);
}

function bareSpreadStr<T extends Array<string>>(...items: T): void {
  for (const s of items) {
    console.log(s);
  }
}

function testBareSpreadStr(): void {
  // @skjs-expect-error Invalid call. Unexpected type for ...
  bareSpreadStr("a", "b", "c");
}
