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

// symbol refinement
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

// Promises are objects and typeof "object" refinement preserves Promise type
function testPromiseAsObject(
  x: Promise<number> | string,
  def: Promise<number>,
): Promise<number> {
  if (typeof x === "object") {
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
function testClassInstanceVsFunction(x: MyClass | (() => void)): MyClass {
  if (typeof x === "function") {
    return new MyClass(0);
  } else {
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof incorrect refinements (should produce errors)
///////////////////////////////////////////////////////////////////////////////

// SKJS correctly refines typeof and catches incorrect return type
function testIncorrectRefinement(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else {
    // This correctly errors - x is string here, not number
    // @skjs-expect-error Invalid return type
    return x;
  }
}

// SKJS correctly rejects functions in typeof === "object" checks
function testFunctionAsObject(x: (() => void) | string): () => void {
  // TODO: warn for condition always false
  if (typeof x === "object") {
    return x;
  } else {
    return () => {};
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

///////////////////////////////////////////////////////////////////////////////
// More negative tests - should detect errors
///////////////////////////////////////////////////////////////////////////////

// Accessing properties on wrong branch
function testAccessWrongBranch(x: { a: number } | string): number {
  if (typeof x === "string") {
    // @skjs-expect-error Invalid return type
    // @ts-expect-error Invalid index key
    return x.a;
  } else {
    return x.a;
  }
}

// Wrong property in refined type
function testWrongProperty(x: { a: number } | { b: string }): number {
  if (typeof x === "object") {
    // Both branches are objects, can't distinguish with typeof
    // @ts-expect-error Invalid return type
    return x.a;
  } else {
    return 0;
  }
}

// Trying to call non-function
function testCallNonFunction(x: number | (() => void)): void {
  if (typeof x === "number") {
    // @ts-expect-error Invalid call
    x();
  }
}

// Wrong assumption about typeof undefined vs null
function testNullVsUndefined(x: null | undefined): null {
  if (typeof x === "undefined") {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    return x;
  }
}

// Multiple typeof checks with wrong return
function testMultipleChecksWrong(
  x: number | string | boolean,
): string | boolean {
  if (typeof x === "number") {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    return x;
  }
}

// Forgetting to handle all cases
function testMissingCase(x: number | string | undefined): number {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return 0;
  }
  // Missing undefined case
  // @ts-expect-error Invalid return type
  return x;
}

// Wrong type in object branch with null
function testObjectWithNullWrong(x: { a: number } | null | string): number {
  if (typeof x === "object") {
    // x could be { a: number } or null
    // @ts-expect-error Type cannot be accessed
    return x.a;
  } else {
    return 0;
  }
}

// Array method on non-array
function testArrayMethodWrong(x: number[] | number): number {
  if (typeof x === "number") {
    // @ts-expect-error Unbound field: length
    return x.length;
  } else {
    return x.length;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Tricky cases with multiple branches
///////////////////////////////////////////////////////////////////////////////

// Three-way typeof check
function testThreeWay(x: number | string | boolean): number | string {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return x;
  } else {
    // x is boolean here
    return x ? "true" : "false";
  }
}

// Four-way typeof check
function testFourWay(
  x: number | string | boolean | undefined,
): number | string {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return x;
  } else if (typeof x === "boolean") {
    return 0;
  } else {
    return "";
  }
}

// Nested typeof with different variable
function testNestedDifferentVar(
  x: number | string,
  y: boolean | string,
): number | boolean {
  if (typeof x === "number") {
    if (typeof y === "boolean") {
      return x;
    } else {
      return 0;
    }
  } else {
    if (typeof y === "boolean") {
      return y;
    } else {
      return 0;
    }
  }
}

// typeof in both branches with different checks
function testBothBranches(
  x: number | string | boolean,
  y: number | string,
): number {
  if (typeof x === "number") {
    if (typeof y === "number") {
      return x;
    } else {
      return 0;
    }
  } else {
    if (typeof y === "number") {
      return y;
    } else {
      return 0;
    }
  }
}

// Refinement with early return
function testEarlyReturn(x: number | string | undefined): number {
  if (typeof x === "undefined") {
    return 0;
  }
  if (typeof x === "string") {
    return 0;
  }
  // x must be number here
  return x;
}

// Multiple variables refined together
function testMultipleVars(
  x: number | string,
  y: number | string,
): [number, number] {
  if (typeof x === "number" && typeof y === "number") {
    return [x, y];
  }
  return [0, 0];
}

///////////////////////////////////////////////////////////////////////////////
// Tricky cases with unions and intersections
///////////////////////////////////////////////////////////////////////////////

// Union of objects with typeof
function testObjectUnion(
  x: { a: number } | { b: string } | number,
): { a: number } | { b: string } {
  if (typeof x === "object") {
    return x;
  } else {
    return { a: 0 };
  }
}

// Intersection with typeof (unusual but valid)
function testIntersectionTypeof(
  x: ({ a: number } & { b: string }) | number,
): number {
  if (typeof x === "number") {
    return x;
  } else {
    return x.a;
  }
}

// Union with never (after exhaustive checks)
function testExhaustiveCheck(x: number | string): never | number | string {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return x;
  } else {
    // x is never here - all cases covered
    return x;
  }
}

// Complex union with overlapping typeof results
function testOverlappingTypeof(
  x: (() => void) | { a: number } | number[] | null,
): (() => void) | { a: number } | number[] | null {
  if (typeof x === "function") {
    return x;
  } else if (typeof x === "object") {
    // x is { a: number } | number[] | null
    return x;
  } else {
    // Unreachable - all are object or function
    return null;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Edge cases with never type
///////////////////////////////////////////////////////////////////////////////

// Never type after impossible refinement
function testNeverAfterRefinement(x: never): number {
  if (typeof x === "number") {
    return x;
  } else {
    return 0;
  }
}

// Union that becomes never after refinement
function testBecomesNever(x: number): string {
  if (typeof x === "string") {
    // This branch is never taken since x is number
    return x;
  } else {
    // @ts-expect-error Invalid return type
    return x;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Incorrect typeof patterns (common mistakes)
///////////////////////////////////////////////////////////////////////////////

// Using typeof with wrong value
function testWrongTypeofValue(x: number | string): number {
  // @ts-expect-error Unexpected typeof check against "array"
  if (typeof x === "array") {
    return 0;
  } else {
    return 0;
  }
}

// Comparing typeof to variable instead of literal
function testTypeofToVariable(x: number | string, type: string): number {
  // SKJS probably won't refine this
  if (typeof x === type) {
    return 0;
  } else {
    return 0;
  }
}

function testDoubleNegation(x: number | string): number {
  if (!(typeof x !== "number")) {
    return x;
  } else {
    return 0;
  }
}

// typeof with strict equality vs loose equality
function testStrictEquality(x: number | string): number {
  // SKJS should only refine with ===
  if (typeof x === "number") {
    return x;
  } else {
    return 0;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Complex real-world scenarios
///////////////////////////////////////////////////////////////////////////////

// Discriminated union with typeof check first
type Action =
  | { type: "increment"; by: number }
  | { type: "decrement"; by: number }
  | number;

function testDiscriminatedWithTypeof(action: Action): number {
  if (typeof action === "number") {
    return action;
  } else if (action.type === "increment") {
    return action.by;
  } else {
    return -action.by;
  }
}

// Optional chaining with typeof
function testOptionalChaining(x: { a?: number } | string): number {
  if (typeof x === "object") {
    return x.a ?? 0;
  } else {
    return 0;
  }
}

// Typeof with destructuring
function testDestructuring(x: { a: number; b: string } | number): number {
  if (typeof x === "object") {
    const { a } = x;
    return a;
  } else {
    return x;
  }
}

// Generic function with typeof
function testGenericTypeof<T extends number | string>(x: T): number {
  if (typeof x === "number") {
    return x;
  } else {
    return 0;
  }
}

// Typeof in callback
function testTypeofInCallback(x: number | string): (y: number) => number {
  return (y: number) => {
    if (typeof x === "number") {
      return x;
    } else {
      return y;
    }
  };
}

// Mixed typeof and property checks
function testMixedChecks(
  x: { kind: "a"; value: number } | { kind: "b"; value: string } | number,
): number {
  if (typeof x === "number") {
    return x;
  } else if (x.kind === "a") {
    return x.value;
  } else {
    return 0;
  }
}

// FIXME: 'as' operator not supported in SKJS
function testWithAssertion(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else {
    // SKJS doesn't support 'as' operator
    // @skjs-expect-error Construction not supported: operator as
    return (x as string).length;
  }
}

// Recursive typeof checks
function testRecursiveTypeof(x: number | string | boolean | null): string {
  if (typeof x === "object") {
    return "null";
  } else if (typeof x === "number") {
    return "number";
  } else if (typeof x === "string") {
    return "string";
  } else {
    return "boolean";
  }
}

// Array.isArray with typeof (different from typeof)
// FIXME: 'as' operator not supported in SKJS
function testArrayIsArray(
  x: number[] | { a: number },
  arr: number[],
): number[] {
  if (typeof x === "object") {
    // Both are objects, typeof can't distinguish
    // Would need Array.isArray for real discrimination
    // @skjs-expect-error Construction not supported: operator as
    return x as number[];
  } else {
    return arr;
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with tuples
///////////////////////////////////////////////////////////////////////////////

// Tuples are typeof "object" and refinement preserves tuple type
function testTupleIsObject(
  x: [number, string] | number,
  def: [number, string],
): [number, string] {
  if (typeof x === "object") {
    return x;
  } else {
    return def;
  }
}

// Tuple vs object with fields
function testTupleVsObject(
  x: [number, string] | { a: number; b: string },
): [number, string] {
  if (typeof x === "object") {
    // Both are objects, typeof can't distinguish
    return [0, ""];
  } else {
    return [0, ""];
  }
}

// Tuple vs array (both are objects)
function testTupleVsArray(
  x: [number, string] | number[],
  arr: number[],
): [number, string] | number[] {
  if (typeof x === "object") {
    // Both tuples and arrays are typeof "object"
    return x;
  } else {
    // @skjs-expect-error Invalid return type
    return arr;
  }
}

// Tuple in union with primitives
function testTupleWithPrimitives(
  x: [number, string] | number | string,
): [number, string] {
  if (typeof x === "object") {
    return x;
  } else if (typeof x === "number") {
    return [x, ""];
  } else {
    return [0, x];
  }
}

// Empty tuple vs non-empty tuple
// FIXME: SKJS doesn't support empty tuple syntax yet
// @skjs-expect-error TODO emptyArray
function testEmptyTuple(x: [] | [number]): [] | [number] {
  if (typeof x === "object") {
    return x;
  } else {
    // TODO: This error won't be reported due to earlier error
    return [];
  }
}

// Tuple with optional elements
// FIXME: SKJS doesn't support optional tuple elements yet
function testTupleOptional(
  // @skjs-expect-error TODO optional element tuple
  x: [number, string?] | number,
  // @skjs-expect-error TODO optional element tuple
): [number, string?] {
  if (typeof x === "object") {
    return x;
  } else {
    // @skjs-expect-error Invalid return type
    return [0];
  }
}

// Tuple vs null
function testTupleVsNull(
  x: [number, string] | null | string,
  def: [number, string],
): [number, string] {
  if (typeof x === "object") {
    // Both tuple and null are typeof "object", need ?? to handle null
    return x ?? def;
  } else {
    return [0, x];
  }
}

// Nested tuples
function testNestedTuples(
  x: [number, [string, boolean]] | number,
): [number, [string, boolean]] {
  if (typeof x === "object") {
    return x;
  } else {
    return [x, ["", false]];
  }
}

// Tuple with union element types
function testTupleWithUnion(
  x: [number | string, boolean] | number,
): [number | string, boolean] {
  if (typeof x === "object") {
    return x;
  } else {
    return [x, false];
  }
}

// Rest elements in tuple
// FIXME: SKJS doesn't support tuple rest elements yet
function testTupleWithRest(
  // @skjs-expect-error TODO tuple spread
  x: [number, ...string[]] | number,
  arr: string[],
): [number, ...string[]] {
  if (typeof x === "object") {
    return x;
  } else {
    return [x, ...arr];
  }
}

// Tuple accessing elements after typeof
function testTupleElementAccess(x: [number, string] | number): number {
  if (typeof x === "object") {
    return x[0];
  } else {
    return x;
  }
}

// Tuple destructuring after typeof
function testTupleDestructuring(x: [number, string] | number): string {
  if (typeof x === "object") {
    const [_n, s] = x;
    return s;
  } else {
    return "";
  }
}

// Multiple tuple types in union
// FIXME: SKJS infers [false] as a 2-element tuple instead of 1-element tuple
function testMultipleTuples(
  x: [number, string] | [boolean] | number,
): [number, string] | [boolean] {
  if (typeof x === "number") {
    return [false];
  } else {
    // TODO: This error won't be reported due to earlier error
    return x;
  }
}

// Tuple vs function
function testTupleVsFunction(
  x: [number, string] | (() => void),
): [number, string] {
  if (typeof x === "function") {
    return [0, ""];
  } else {
    return x;
  }
}

// Labeled tuple elements
// FIXME: SKJS doesn't support labeled tuple elements yet
function testLabeledTuple(
  // @skjs-expect-error TODO named tuple
  x: [first: number, second: string] | number,
  // @skjs-expect-error TODO named tuple
): [first: number, second: string] {
  if (typeof x === "object") {
    return x;
  } else {
    return [x, ""];
  }
}

// Readonly tuple
// FIXME: SKJS doesn't support readonly tuples yet
function testReadonlyTuple(
  // @skjs-expect-error TODO readonly
  x: readonly [number, string] | number,
  // @skjs-expect-error TODO readonly
): readonly [number, string] {
  if (typeof x === "object") {
    return x;
  } else {
    return [x, ""];
  }
}

// Tuple with typeof check on element
function testTupleElementTypeof(x: [number | string, boolean]): number {
  const [first, _second] = x;
  if (typeof first === "number") {
    return first;
  } else {
    return 0;
  }
}

// Complex tuple union after typeof refinement
function testComplexTupleUnion(
  x: [number, string] | [boolean, number] | string,
): [number, string] | [boolean, number] {
  if (typeof x === "string") {
    return [0, x];
  } else {
    return x;
  }
}

// Tuple in intersection (unusual but valid)
function testTupleIntersection(
  x: ([number, string] & { length: 2 }) | number,
): number {
  if (typeof x === "number") {
    return x;
  } else {
    return x[0];
  }
}

// Wrong tuple element access after typeof
function testWrongTupleAccess(x: [number, string] | string): string {
  if (typeof x === "string") {
    return x;
  } else {
    // Accessing tuple[1] is valid, returns string
    return x[1];
  }
}

// Tuple with never elements
function testTupleWithNever(x: [number, never] | string): string {
  if (typeof x === "string") {
    return x;
  } else {
    // tuple with never is essentially unreachable
    return "";
  }
}

// Tuple spread in return
// FIXME: SKJS doesn't support tuple spread syntax yet
function testTupleSpread(
  x: [number, string] | number,
): [number, string, boolean] {
  if (typeof x === "object") {
    // TODO be more precise with tuples
    // @skjs-expect-error Invalid return type
    return [...x, false];
  } else {
    return [x, "", false];
  }
}

///////////////////////////////////////////////////////////////////////////////
// typeof with tuples - negative tests
///////////////////////////////////////////////////////////////////////////////

// Wrong index access
function testTupleWrongIndex(x: [number, string] | number): boolean {
  if (typeof x === "object") {
    // Accessing out of bounds
    // @skjs-expect-error Invalid return type
    return x[2];
  } else {
    return false;
  }
}

// Wrong destructuring count
function testTupleWrongDestructure(x: [number, string] | number): boolean {
  if (typeof x === "object") {
    // @ts-expect-error Invalid tuple pattern size, it is of size 3
    const [_a, _b, c] = x;
    return c;
  } else {
    return false;
  }
}

// Treating tuple as array with methods
// FIXME: map method for tuples
function testTupleArrayMethod(x: [number, string] | number): number {
  if (typeof x === "object") {
    // Tuples don't have array methods in SKJS
    // @skjs-expect-error Please add a type annotation
    return x.map((v) => v).length;
  } else {
    return x;
  }
}

// Wrong tuple element type
function testWrongTupleElementType(
  x: [number, string] | string,
): [string, string] {
  if (typeof x === "object") {
    // @ts-expect-error Invalid return type
    return x;
  } else {
    return [x, x];
  }
}
