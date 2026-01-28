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
function testBasicArrayRefinement(x: Array<number> | Foo): Array<number> {
  if (Array.isArray(x)) {
    // x should be refined to Array<number>
    // @skjs-expect-error Invalid return type
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
    // x is now refined to Foo
    // @skjs-expect-error Invalid return type
    return x;
  }
}

// Test with different array type
function testStringArrayRefinement(x: Array<string> | Foo): Array<string> {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
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
    // @skjs-expect-error Invalid return type
    return x.length;
  } else {
    return 0;
  }
}

function testArrayPushAfterRefinement(x: Array<number> | Foo): void {
  if (Array.isArray(x)) {
    // Should be able to call array methods
    // @skjs-expect-error Invalid call
    x.push(42);
  }
}

///////////////////////////////////////////////////////////////////////////////
// Multiple union types
///////////////////////////////////////////////////////////////////////////////

function testMultipleUnion(x: Array<number> | Foo | string): Array<number> {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    return [];
  }
}

function testMultipleUnionElseBranch(
  x: Array<number> | Foo | string,
): Foo | string {
  if (Array.isArray(x)) {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    // x is now refined to Foo | string (no array)
    // @skjs-expect-error Invalid return type
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Nested refinement
///////////////////////////////////////////////////////////////////////////////

function testNestedRefinement(x: Array<number> | Foo | null): Array<number> {
  if (x === null) {
    return [];
  } else if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
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
function testArrayMethodOnNonArray(x: Array<number> | Foo): number {
  if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x.length;
  } else {
    // x is now refined to Foo (no length property)
    // @ts-expect-error Invalid return type
    return x.length;
  }
}

// Wrong type in array branch
function testWrongTypeInArrayBranch(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    // x is now refined to Foo, so this should work
    // @skjs-expect-error Invalid return type
    return x;
  }
}

// Else branch with refinement
function testElseBranchRefined(x: Array<number> | Foo): Foo {
  if (Array.isArray(x)) {
    return { a: "", b: 0 };
  } else {
    // x is now refined to Foo
    // @skjs-expect-error Invalid return type
    return x;
  }
}

// Accessing object properties on array branch
function testObjectPropOnArray(x: Array<number> | Foo): string {
  if (Array.isArray(x)) {
    // @ts-expect-error Invalid return type
    return x.a;
  } else {
    // x is now refined to Foo, so x.a works
    // @skjs-expect-error Invalid return type
    return x.a;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Early return pattern
///////////////////////////////////////////////////////////////////////////////

function testEarlyReturn(x: Array<number> | Foo): Array<number> {
  if (!Array.isArray(x)) {
    return [];
  }
  // x should be refined to Array<number> here
  // @skjs-expect-error Invalid return type
  return x;
}

function testEarlyReturnWithLength(x: Array<number> | Foo): number {
  if (!Array.isArray(x)) {
    return 0;
  }
  // x should be Array<number>, can access length
  // @skjs-expect-error Invalid return type
  return x.length;
}

///////////////////////////////////////////////////////////////////////////////
// Combined with typeof
///////////////////////////////////////////////////////////////////////////////

function testCombinedWithTypeof(
  x: Array<number> | Foo | string,
): Array<number> {
  if (typeof x === "string") {
    return [];
  } else if (Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    return [];
  }
}
