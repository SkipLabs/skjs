// Tests for symbol and unique symbol type support

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
    // @skjs-expect-error Invalid return type
    return x; // x is narrowed to symbol here
  } else {
    return Symbol("default");
  }
}

function refineAwaySymbol(x: symbol | string): string {
  if (typeof x === "symbol") {
    return "was a symbol";
  } else {
    // @skjs-expect-error Invalid return type
    return x; // x is narrowed to string here
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 4: unique symbol type
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error TODO uniqueSymbol
const uniqueSym1: unique symbol = Symbol();

// @skjs-expect-error TODO uniqueSymbol
const uniqueSym2: unique symbol = Symbol("unique");

///////////////////////////////////////////////////////////////////////////////
// Test 5: unique symbol must be const (will be tested once unique symbol works)
///////////////////////////////////////////////////////////////////////////////

// TODO: Test that unique symbol requires const declaration
// Currently SKJS doesn't support top-level let, so we can't test this yet

///////////////////////////////////////////////////////////////////////////////
// Test 6: unique symbols are distinct types (will be tested once they work)
///////////////////////////////////////////////////////////////////////////////

// TODO: Once unique symbols are implemented, test that:
// - Each unique symbol declaration creates a distinct type
// - unique symbol A is not assignable to unique symbol B
// - unique symbol is assignable to symbol (covariance)
// - symbol is NOT assignable to unique symbol (contravariance)

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
// Test 8: Symbol as object key type (future enhancement)
///////////////////////////////////////////////////////////////////////////////

// These will fail until symbol-named properties are supported
// const mySymbol = Symbol("myKey");
// const obj = {
//   [mySymbol]: "value"
// };

///////////////////////////////////////////////////////////////////////////////
// Test 9: Well-known symbols (future enhancement)
///////////////////////////////////////////////////////////////////////////////

// function testIterator(): void {
//   const arr = [1, 2, 3];
//   const iterator = arr[Symbol.iterator]();
//   console.log(iterator.next());
// }

///////////////////////////////////////////////////////////////////////////////
// Test 10: typeof symbol with null/undefined
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
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    return Symbol("default");
  }
}
