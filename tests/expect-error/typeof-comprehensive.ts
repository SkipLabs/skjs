///////////////////////////////////////////////////////////////////////////////
// Comprehensive typeof tests
// SKJS refines types within if (typeof x === "...") { } else { } constructs
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic primitive type refinement
///////////////////////////////////////////////////////////////////////////////

// number refinement
function testNumberRefinement(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else {
    return 0;
  }
}

// string refinement
function testStringRefinement(x: number | string): string {
  if (typeof x === "string") {
    return x;
  } else {
    return "";
  }
}

// boolean refinement
function testBooleanRefinement(x: boolean | string): boolean {
  if (typeof x === "boolean") {
    return x;
  } else {
    return false;
  }
}

// undefined refinement
function testUndefinedRefinement(x: number | undefined): number {
  if (typeof x === "undefined") {
    return 0;
  } else {
    return x;
  }
}

// bigint refinement
function testBigintRefinement(x: bigint | number): bigint {
  if (typeof x === "bigint") {
    return x;
  } else {
    return 0n;
  }
}

// FIXME: symbol type not supported in SKJS
// @skjs-expect-error Type symbol not found
function testSymbolRefinement(x: symbol | string, sym: symbol): symbol {
  if (typeof x === "symbol") {
    return x;
  } else {
    return sym;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Negative refinement (else branch)
///////////////////////////////////////////////////////////////////////////////

function testNegativeNumberRefinement(x: number | string): string {
  if (typeof x === "number") {
    return "";
  } else {
    return x;
  }
}

function testNegativeStringRefinement(x: number | string): number {
  if (typeof x === "string") {
    return 0;
  } else {
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Multiple union types refinement
///////////////////////////////////////////////////////////////////////////////

function testMultipleUnionRefinement(x: number | string | boolean): number {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return 0;
  } else {
    return 1;
  }
}

function testMultipleUnionRefinement2(
  x: number | string | boolean,
): string | boolean {
  if (typeof x === "number") {
    return "";
  } else {
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with objects - tricky cases
///////////////////////////////////////////////////////////////////////////////

// typeof returns "object" for objects, arrays, and null
function testObjectRefinement(x: { a: number } | string): { a: number } {
  if (typeof x === "object") {
    // x could be { a: number } or null here in JavaScript
    // but SKJS should refine to { a: number }
    return x;
  } else {
    return { a: 0 };
  }
}

// Arrays are also "object"
// FIXME: Empty array literal [] creates tuple type in SKJS, not array type
function testArrayAsObject(x: number[] | string, emptyArr: number[]): number[] {
  if (typeof x === "object") {
    return x;
  } else {
    return emptyArr;
  }
}

// Object vs string
function testObjectVsString(x: { field: string } | string): { field: string } {
  if (typeof x === "object") {
    return x;
  } else {
    return { field: "" };
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with null - tricky case
///////////////////////////////////////////////////////////////////////////////

// In JavaScript, typeof null === "object" (famous bug)
// This tests how SKJS handles it
function testNullAsObject(x: null | string): string {
  if (typeof x === "object") {
    // In JavaScript this branch is taken for null
    // SKJS should handle this correctly
    return "";
  } else {
    return x;
  }
}

function testNullInUnion(x: { a: number } | null | string): { a: number } {
  if (typeof x === "object") {
    // x could be { a: number } or null
    // SKJS needs to refine this properly
    return x ?? { a: 0 };
  } else {
    return { a: 0 };
  }
}

// undefined is distinct from null
function testUndefinedVsNull(x: undefined | null): undefined {
  if (typeof x === "undefined") {
    return x;
  } else {
    return undefined;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with functions
///////////////////////////////////////////////////////////////////////////////

function testFunctionRefinement(x: (() => number) | string): () => number {
  if (typeof x === "function") {
    return x;
  } else {
    return () => 0;
  }
}

function testFunctionVsObject(x: (() => void) | { a: number }): () => void {
  if (typeof x === "function") {
    return x;
  } else {
    return () => {};
  }
}

// Function with different signatures
function testFunctionUnion(
  x: ((n: number) => number) | ((s: string) => string) | number,
): ((n: number) => number) | ((s: string) => string) {
  if (typeof x === "function") {
    return x;
  } else {
    return (n: number) => n;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with callable objects (objects with call signatures)
///////////////////////////////////////////////////////////////////////////////

// Callable object - has both properties and can be called
type CallableObject = {
  (x: number): number;
  property: string;
};

function testCallableObject(x: CallableObject | string): CallableObject {
  if (typeof x === "function") {
    // Callable objects are typeof "function"
    return x;
  } else {
    const fn: CallableObject = Object.assign((n: number) => n, {
      property: "",
    });
    return fn;
  }
}

// Callable vs regular object
function testCallableVsObject(x: { (n: number): number } | { field: number }): {
  (n: number): number;
} {
  if (typeof x === "function") {
    return x;
  } else {
    return (n: number) => n;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with complex union types
///////////////////////////////////////////////////////////////////////////////

function testComplexUnion(
  x: number | string | { a: number } | (() => void),
): number | string {
  if (typeof x === "object") {
    return 0;
  } else if (typeof x === "function") {
    return 0;
  } else {
    return x;
  }
}

// FIXME: After all typeof checks, SKJS infers optional field instead of required field
function testComplexUnion2(
  x: number | string | { a: number } | (() => void) | undefined,
): { a: number } {
  if (typeof x === "number") {
    return { a: 0 };
  } else if (typeof x === "string") {
    return { a: 0 };
  } else if (typeof x === "undefined") {
    return { a: 0 };
  } else if (typeof x === "function") {
    return { a: 0 };
  } else {
    // @skjs-expect-error Invalid return type
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with promises - tricky case
///////////////////////////////////////////////////////////////////////////////

// Promises are objects
// FIXME: SKJS typeof refinement doesn't narrow x correctly for Promise
function testPromiseAsObject(
  x: Promise<number> | string,
  def: Promise<number>,
): Promise<number> {
  if (typeof x === "object") {
    // @skjs-expect-error Invalid return type
    return x;
  } else {
    return def;
  }
}

// Promise vs function
function testPromiseVsFunction(
  x: Promise<number> | (() => number),
  def: Promise<number>,
): Promise<number> {
  if (typeof x === "function") {
    return def;
  } else {
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with nested refinements
///////////////////////////////////////////////////////////////////////////////

function testNestedRefinement(
  x: number | string | { a: number } | undefined,
): number {
  if (typeof x === "undefined") {
    return 0;
  } else {
    if (typeof x === "number") {
      return x;
    } else if (typeof x === "string") {
      return 0;
    } else {
      return x.a;
    }
  }
}

function testNestedRefinement2(
  x: number | string | boolean | null,
): number | string {
  if (typeof x === "object") {
    // x is null here
    return 0;
  } else {
    if (typeof x === "boolean") {
      return "";
    } else {
      return x;
    }
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with class instances
///////////////////////////////////////////////////////////////////////////////

class MyClass {
  field: number;
  constructor(field: number) {
    this.field = field;
  }
}

// Class instances are objects
function testClassInstance(x: MyClass | string): MyClass {
  if (typeof x === "object") {
    return x;
  } else {
    return new MyClass(0);
  }
}

// Class instance vs function
// FIXME: SKJS typeof refinement makes class field optional after function check
function testClassInstanceVsFunction(x: MyClass | (() => void)): MyClass {
  if (typeof x === "function") {
    return new MyClass(0);
  } else {
    // @skjs-expect-error Invalid return type
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof incorrect refinements (should produce errors)
///////////////////////////////////////////////////////////////////////////////

// FIXME: TypeScript refines typeof correctly and catches this error, but SKJS doesn't
function testIncorrectRefinement(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else {
    // This should error - x is string here, not number
    // @skjs-expect-error Invalid return type
    return x;
  }
}

function testIncorrectNullHandling(x: { a: number } | null): { a: number } {
  if (typeof x === "object") {
    // x could be null here, so this should error
    // @ts-expect-error Invalid return type
    return x;
  } else {
    return { a: 0 };
  }
}

function testIncorrectFunctionRefinement(x: (() => number) | string): string {
  if (typeof x === "function") {
    // This should error - x is function here, not string
    // @ts-expect-error Invalid return type
    return x;
  } else {
    return x;
  }
}
