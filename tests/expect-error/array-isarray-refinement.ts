///////////////////////////////////////////////////////////////////////////////
// Array.isArray refinement tests
// Tests that Array.isArray correctly refines Array<T> | OtherType to Array<T>
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic Array.isArray refinement
///////////////////////////////////////////////////////////////////////////////

type Foo = {
  a: string;
  b: number;
};

// Test basic refinement - Array | Foo
function testBasicArrayRefinement(x: Array<number> | Foo): Array<unknown> {
  if (Array.isArray(x)) {
    // x should be refined to Array<number>
    return x;
  } else {
    return [];
  }
}

// Test negative refinement - else branch is refined to Foo
function testNegativeArrayRefinement(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    return { a: "", b: 0 };
  } else {
    // x is refined to Foo
    return x;
  }
}

// Test with different array type
function testStringArrayRefinement(x: Array<string> | Foo): Array<unknown> {
  if (Array.isArray(x)) {
    return x;
  } else {
    return [];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Array methods should work after refinement
///////////////////////////////////////////////////////////////////////////////

function testArrayMethodsAfterRefinement(x: Array<number> | Foo): number {
  if (Array.isArray(x)) {
    // Should be able to access array properties and methods
    return x.length;
  } else {
    return 0;
  }
}

function testArrayPushAfterRefinement(x: Array<number> | Foo): void {
  if (Array.isArray(x)) {
    // Should be able to call array methods
    x.push(42);
  }
}

///////////////////////////////////////////////////////////////////////////////
// Multiple union types
///////////////////////////////////////////////////////////////////////////////

function testMultipleUnion(x: Array<number> | Foo | string): Array<unknown> {
  if (Array.isArray(x)) {
    return x;
  } else {
    return [];
  }
}

function testMultipleUnionElseBranch(
  x: Array<number> | Foo | string,
): Foo | string {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    // x is refined to Foo | string (no array)
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Nested refinement
///////////////////////////////////////////////////////////////////////////////

function testNestedRefinement(x: Array<number> | Foo | null): Array<unknown> {
  if (x === null) {
    return [];
  } else if (Array.isArray(x)) {
    return x;
  } else {
    return [];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Array.isArray with complex types
///////////////////////////////////////////////////////////////////////////////

type Bar = {
  c: boolean;
};

function testComplexUnion(x: Array<string> | Foo | Bar): Array<string> {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    return [];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Negative tests - should produce errors
///////////////////////////////////////////////////////////////////////////////

// Accessing array methods - now with refinement
function testArrayMethodOnNonArray(x: Array<number> | Foo): unknown {
  if (Array.isArray(x)) {
    return x.length;
  } else {
    // @skjs-expect-error Unbound field: length
    return x.length;
  }
}

// Wrong type in array branch
function testWrongTypeInArrayBranch(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    // x is refined to Foo
    return x;
  }
}

// Else branch with refinement
function testElseBranchRefined(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    return { a: "", b: 0 };
  } else {
    // x is refined to Foo
    return x;
  }
}

// Accessing object properties on array branch
function testObjectPropOnArray(x: Array<number> | Foo): unknown {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid index key
    return x.a;
  } else {
    // x is refined to Foo, x.a is valid
    return x.a;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Early return pattern
///////////////////////////////////////////////////////////////////////////////

function testEarlyReturn(x: Array<number> | Foo): Array<unknown> {
  if (!Array.isArray(x)) {
    return [];
  }
  // x should be refined to Array<unknown> here
  return x;
}

function testEarlyReturnWithLength(x: Array<number> | Foo): number {
  if (!Array.isArray(x)) {
    return 0;
  }
  // x should be Array<number>, can access length
  return x.length;
}

///////////////////////////////////////////////////////////////////////////////
// Combined with typeof
///////////////////////////////////////////////////////////////////////////////

function testCombinedWithTypeof(
  x: Array<number> | Foo | string,
): Array<unknown> {
  if (typeof x === "string") {
    return [];
  } else if (Array.isArray(x)) {
    return x;
  } else {
    return [];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Negative refinement combined with other checks
///////////////////////////////////////////////////////////////////////////////

function testNegativeWithNull(x: Array<number> | Foo | null): Foo {
  if (x === null) {
    return { a: "", b: 0 };
  } else if (Array.isArray(x)) {
    return { a: "", b: 0 };
  } else {
    // x is refined to Foo (null and Array eliminated)
    return x;
  }
}

function testMultipleArrays(x: Array<string> | Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    return { a: "", b: 0 };
  } else {
    // Both Array<string> and Array<number> are eliminated
    return x;
  }
}

// After negative refinement, Foo fields should be accessible
function testFieldAccessAfterNegative(x: Array<number> | Foo): string {
  if (Array.isArray(x)) {
    return "";
  }
  // x is refined to Foo
  return x.a;
}

// After negative refinement via early return
function testNegativeEarlyReturn(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    return { a: "", b: 0 };
  }
  // x is refined to Foo
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Tuple types interact correctly with Array.isArray
///////////////////////////////////////////////////////////////////////////////

// Tuples survive positive Array.isArray branch
function testTuplePositive(x: [number, string] | number): [number, string] {
  if (Array.isArray(x)) {
    return x;
  } else {
    return [0, ""];
  }
}

// Tuples removed in negative Array.isArray branch
function testTupleNegative(x: [number, string] | number): number {
  if (!Array.isArray(x)) {
    // tuple is eliminated, x is number
    return x;
  }
  return 0;
}

///////////////////////////////////////////////////////////////////////////////
// Object literal expressions have isArray=false and cannot fake Array.isArray
///////////////////////////////////////////////////////////////////////////////

// An object literal expression that structurally matches Array is eliminated
// in the positive Array.isArray branch because it has isArray=false.
function testObjectLiteralEliminatedInPositiveBranch(): number {
  const x = { length: 42, push(elt: number): void {} };
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid access for type never
    return x.length;
  } else {
    return x.length;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Class instances have isArray=false and are eliminated by Array.isArray
///////////////////////////////////////////////////////////////////////////////

class NumHolder<T> {
  value: T;
  constructor(v: T) {
    this.value = v;
  }
}

// TODO: Class instances should have isArray=false and be eliminated in the
// positive Array.isArray branch.
function testClassInstanceNotArray(x: NumHolder<number>): number {
  if (Array.isArray(x)) {
    return x.value;
  } else {
    return x.value;
  }
}
