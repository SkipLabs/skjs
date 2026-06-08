// Tests for symbol and unique symbol type support

///////////////////////////////////////////////////////////////////////////////
// Test 0: Importing unique symbols
///////////////////////////////////////////////////////////////////////////////

import { exportedUniqueSymbol } from "./symbols-export.js";

const importedSym: typeof exportedUniqueSymbol = exportedUniqueSymbol;

///////////////////////////////////////////////////////////////////////////////
// Test 1: Basic symbol type annotations
///////////////////////////////////////////////////////////////////////////////

function basicSymbolParam(s: symbol): void {
  console.log(s);
}

function basicSymbolReturn(): symbol {
  return Symbol("test");
}

const sym1: symbol = Symbol();

const sym2: symbol = Symbol("description");

///////////////////////////////////////////////////////////////////////////////
// Test 2: Symbol in union types
///////////////////////////////////////////////////////////////////////////////

function symbolOrString(x: symbol | string): string {
  if (typeof x === "string") {
    return x;
  } else {
    return String(x);
  }
}

function symbolOrNumber(x: symbol | number): number {
  if (typeof x === "number") {
    return x;
  } else {
    return 0;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: typeof refinement with symbol
///////////////////////////////////////////////////////////////////////////////

function refineToSymbol(x: symbol | string): symbol {
  if (typeof x === "symbol") {
    return x; // x is narrowed to symbol here
  } else {
    return Symbol("default");
  }
}

function refineAwaySymbol(x: symbol | string): string {
  if (typeof x === "symbol") {
    return "was a symbol";
  } else {
    return x; // x is narrowed to string here
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 4: unique symbol type
///////////////////////////////////////////////////////////////////////////////

// Top-level const with unique symbol works correctly
const uniqueSym1: unique symbol = Symbol();

const uniqueSym2: unique symbol = Symbol("unique");

///////////////////////////////////////////////////////////////////////////////
// Test 5: unique symbol can only be used in top-level const declarations
///////////////////////////////////////////////////////////////////////////////

// unique symbol cannot be used in function parameters
// @skjs-expect-error unique symbol type cannot be used here
function takesUniqueSymbol(s: unique symbol): void {
  console.log(s);
}

// unique symbol cannot be used in function return types
// @skjs-expect-error unique symbol type cannot be used here
function returnsUniqueSymbol(): unique symbol {
  return Symbol();
}

// unique symbol cannot be used in local const declarations
// Rationale: the unique identifier we use is based on the position
function localUniqueSymbol(): void {
  // @skjs-expect-error unique symbol type cannot be used here
  const localSym: unique symbol = Symbol();
}

// FIXME (maybe): unique symbol is allowed here for declared const
// unique symbol in object property types is allowed for top-level const,
// but Symbol() returns symbol, not a specific unique symbol
// @skjs-expect-error Invalid definition: value type is not compatible with type annotation
// @skjs-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const objWithUniqueSymbol: { prop: unique symbol } = { prop: Symbol() };

///////////////////////////////////////////////////////////////////////////////
// Test 6: unique symbols are distinct types
///////////////////////////////////////////////////////////////////////////////

// Each unique symbol declaration creates a distinct type
const uniqueA: unique symbol = Symbol("a");
const uniqueB: unique symbol = Symbol("b");

// unique symbol A is not assignable to unique symbol B
function testDistinctTypes(): void {
  // @skjs-expect-error Invalid annotation
  // @skjs-expect-error-line2 Type typeof uniqueB
  // @skjs-expect-error-line3 is not compatible with type typeof uniqueA
  // @skjs-expect-error-line4 Value typeof uniqueB is missing
  const b: typeof uniqueA = uniqueB; // Different unique symbols are incompatible
}

// Local const cannot use unique symbol (only top-level const allowed)
// Rationale: the unique identifier we use is based on the position
function testLocalUniqueSymbol(): void {
  // @skjs-expect-error unique symbol type cannot be used here
  const a: unique symbol = Symbol("a");
}

// unique symbol cannot be used in function parameters
// @skjs-expect-error unique symbol type cannot be used here
function testCovariance(us: unique symbol): symbol {
  return us;
}

// symbol is not assignable to unique symbol
function testContravariance(s: symbol): void {
  // @skjs-expect-error Invalid annotation
  // @skjs-expect-error-line2 Full type symbol
  // @skjs-expect-error-line3 is not compatible with specific type typeof uniqueA
  const us: typeof uniqueA = s; // symbol → unique symbol should fail
}

///////////////////////////////////////////////////////////////////////////////
// Test 7: Symbol values at runtime
///////////////////////////////////////////////////////////////////////////////

function symbolAtRuntime(): void {
  const s1 = Symbol();
  const s2 = Symbol("key");

  const s3 = Symbol.for("global");

  // Symbols are unique - each call to Symbol() creates a distinct value
  if (s1 === s2) {
    console.log("never happens - symbols are always unique");
  }

  // TODO: Symbol.for creates registered symbols (not yet supported)
  // if (s3 === Symbol.for("global")) {
  //   console.log("same symbol");
  // }
}

///////////////////////////////////////////////////////////////////////////////
// Test 8: Symbol-keyed property in type definition (declare const is lazy)
///////////////////////////////////////////////////////////////////////////////

// declare const with symbol field doesn't error at declaration site
// (the type is lazily normalized - errors appear when accessed)
declare const withSymbolField: { [Symbol.iterator]: () => void };

///////////////////////////////////////////////////////////////////////////////
// Test 9: Computed property in object literal expression
///////////////////////////////////////////////////////////////////////////////

function testSymObj(): void {
  const symObj = { [Symbol.iterator]: () => {} };
}

///////////////////////////////////////////////////////////////////////////////
// Test 10: Symbol property access (requires symbol fields in types)
///////////////////////////////////////////////////////////////////////////////

function testIterFn(): void {
  const iterFn: () => void = withSymbolField[Symbol.iterator];
}

///////////////////////////////////////////////////////////////////////////////
// Test 11: for...in does not enumerate symbol properties
///////////////////////////////////////////////////////////////////////////////

function testForInWithSymbols(obj: {
  a: number;
  [Symbol.iterator]: () => void;
}): void {
  for (const k in obj) {
    const s: string = k; // k should always be string, not string | symbol
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 12: 'in' operator with symbol key
///////////////////////////////////////////////////////////////////////////////

const inResult = Symbol.iterator in {};

///////////////////////////////////////////////////////////////////////////////
// Test 13: typeof symbol with null/undefined
///////////////////////////////////////////////////////////////////////////////

function symbolOrNull(x: symbol | null): symbol | null {
  if (typeof x === "symbol") {
    return x;
  } else {
    return null;
  }
}

function symbolOrUndefined(x: symbol | undefined): symbol {
  if (typeof x === "symbol") {
    return x;
  } else {
    return Symbol("default");
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 14: Exported unique symbols
///////////////////////////////////////////////////////////////////////////////

// Exported unique symbol works correctly
export const exportedUniqueSym: unique symbol = Symbol();

///////////////////////////////////////////////////////////////////////////////
// Test 15: Static readonly class members with unique symbol
///////////////////////////////////////////////////////////////////////////////

class MyClass {
  // Static readonly unique symbol works correctly
  static readonly classSym: unique symbol = Symbol();
}

///////////////////////////////////////////////////////////////////////////////
// Test 16: Declare const with unique symbol
///////////////////////////////////////////////////////////////////////////////

// declare const allows unique symbol (works correctly)
declare const declaredSym: unique symbol;

// @skjs-expect-error A property whose type is 'unique symbol' must be 'readonly'
declare const declaredObj: { a: unique symbol };

declare const declaredObjOk: { readonly a: unique symbol };

///////////////////////////////////////////////////////////////////////////////
// Test 17: Well-known symbols
///////////////////////////////////////////////////////////////////////////////

// Well-known symbols are accessible as properties on Symbol
const iteratorSym: symbol = Symbol.iterator;
const asyncIteratorSym: symbol = Symbol.asyncIterator;
const toStringTagSym: symbol = Symbol.toStringTag;
const hasInstanceSym: symbol = Symbol.hasInstance;
const toPrimitiveSym: symbol = Symbol.toPrimitive;

///////////////////////////////////////////////////////////////////////////////
// Test 18: Bracket assignment with symbol key grows local object
///////////////////////////////////////////////////////////////////////////////

function testBracketAssignSymbol(): void {
  let obj = {};
  obj[Symbol.iterator] = () => {};
  // After bracket assignment, obj should have the symbol field.
  const typed: { [Symbol.iterator]: () => void } = obj;
}

///////////////////////////////////////////////////////////////////////////////
// Test 19: Bracket assignment with string literal key grows local object
///////////////////////////////////////////////////////////////////////////////

function testBracketAssignString(): void {
  let obj = {};
  obj["foo"] = 42;
  // After bracket assignment, obj should have the "foo" field.
  const typed: { foo: number } = obj;
}

///////////////////////////////////////////////////////////////////////////////
// Test 20: for...of with Symbol.iterator protocol
///////////////////////////////////////////////////////////////////////////////

function testForOfWithIterator(obj: {
  [Symbol.iterator](): { next(): { value: number; done: boolean } };
}): void {
  for (const x of obj) {
    const n: number = x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 21: for...of on Array (works via indexes today)
///////////////////////////////////////////////////////////////////////////////

function testForOfArray(): void {
  const arr: Array<number> = [1, 2, 3];
  for (const x of arr) {
    const n: number = x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 22: for...of on Set
///////////////////////////////////////////////////////////////////////////////

function testForOfSet(): void {
  const s = new Set<number>([1, 2, 3]);
  for (const x of s) {
    const n: number = x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 23: for...of on Map
///////////////////////////////////////////////////////////////////////////////

function testForOfMap(): void {
  const m = new Map<string, number>([["a", 1]]);
  for (const entry of m) {
    const pair: [string, number] = entry;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 24: for...of on MapIterator
///////////////////////////////////////////////////////////////////////////////

function testForOfMapIterator(): void {
  const m = new Map<string, number>([["a", 1]]);
  for (const k of m.keys()) {
    const s: string = k;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 25: Spread iterable in function call
///////////////////////////////////////////////////////////////////////////////

function spreadTarget(...args: number[]): void {}

function testSpreadIterableInCall(): void {
  const s = new Set<number>([1, 2, 3]);
  spreadTarget(...s);
}

///////////////////////////////////////////////////////////////////////////////
// Test 26: Array destructuring with Array<T>
///////////////////////////////////////////////////////////////////////////////

function testDestructureArray(): void {
  const arr: Array<number> = [1, 2, 3];
  const [a, b] = arr;
  // Elements from iterable destructuring are T | undefined
  const nOk: number | undefined = a;
  // @skjs-expect-error Invalid annotation
  const nBad: number = a;
}

///////////////////////////////////////////////////////////////////////////////
// Test 27: Spread in array literal
///////////////////////////////////////////////////////////////////////////////

function testSpreadInArrayLiteral(): void {
  const s = new Set<number>([1, 2, 3]);
  const arr: Array<number> = [...s];
}

///////////////////////////////////////////////////////////////////////////////
// Test 28: typeof access to a class static unique symbol
///////////////////////////////////////////////////////////////////////////////

// symbol is not assignable to a class static unique symbol
function testClassSymContravariance(s: symbol): void {
  // @skjs-expect-error Invalid annotation
  // @skjs-expect-error-line2 Full type symbol
  // @skjs-expect-error-line3 is not compatible with specific type typeof MyClass.classSym
  const c: typeof MyClass.classSym = s;
}

///////////////////////////////////////////////////////////////////////////////
// Test 29: Anonymous unique symbol (no binding name) shows file + symbol
///////////////////////////////////////////////////////////////////////////////

declare const anonObj: { readonly prop: unique symbol };

function testAnonUniqueSymbol(s: symbol): void {
  // @skjs-expect-error Invalid annotation
  // @skjs-expect-error-line2 Full type symbol
  // @skjs-expect-error-line3 is not compatible with specific type unique symbol defined in tests/expect-error/symbols.ts at constant(anonObj)
  const c: typeof anonObj.prop = s;
}

///////////////////////////////////////////////////////////////////////////////
// Test 30: Symbol-keyed field access is type-checked in both directions
//
// A *specific* unique symbol is a literal key: it names exactly that declared
// field, so both the read (getter) and the write (setter) are checked against
// the declared field type. (A *general* `symbol` key is non-literal and instead
// unions/intersects every symbol field with the symbol index — see
// index-signatures.ts Test 27.)
///////////////////////////////////////////////////////////////////////////////

declare const symField: unique symbol;

function symFieldRead(x: { [symField]: number }): number {
  return x[symField];
}

function symFieldWriteOk(x: { [symField]: number }): void {
  x[symField] = 5;
}

function symFieldWriteChecksSetter(x: { [symField]: number }): void {
  // @skjs-expect-error Invalid assignment
  x[symField] = "no";
}
