///////////////////////////////////////////////////////////////////////////////
// Tests for postfix exclamation mark (non-null assertion operator)
// FIXME: SKJS does not support the postfix ! operator yet
// All these tests should succeed once the operator is implemented
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic non-null assertions
///////////////////////////////////////////////////////////////////////////////

function testBasicNonNull(x: number | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testBasicNonUndefined(x: number | undefined): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testBasicNonNullOrUndefined(x: number | null | undefined): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testStringNonNull(x: string | null): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testBooleanNonNull(x: boolean | null): boolean {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with objects
///////////////////////////////////////////////////////////////////////////////

function testObjectNonNull(x: { field: number } | null): { field: number } {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testObjectFieldAccess(x: { field: number } | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field;
}

function testNestedObjectNonNull(x: { a: { b: number } } | null): {
  a: { b: number };
} {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testNestedObjectFieldAccess(x: { a: { b: number } } | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.a.b;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with arrays
///////////////////////////////////////////////////////////////////////////////

function testArrayNonNull(x: number[] | null): number[] {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testArrayAccess(x: number[] | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0];
}

function testArrayOfObjectsNonNull(
  x: { field: number }[] | null,
): { field: number }[] {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testArrayOfObjectsAccess(x: { field: number }[] | null): number {
  // @skjs-expect-error Property access is not allowed on this type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0].field;
}

function testArrayOfObjectsAccess2(x: { field: number }[] | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0]!.field;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with tuples
///////////////////////////////////////////////////////////////////////////////

function testTupleNonNull(x: [number, string] | null): [number, string] {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testTupleAccess(x: [number, string] | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0];
}

function testTupleDestructuring(x: [number, string] | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  const [n, _s] = x!;
  return n;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with functions
///////////////////////////////////////////////////////////////////////////////

function testFunctionNonNull(x: (() => number) | null): () => number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testFunctionCall(x: (() => number) | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!();
}

function testFunctionWithParamsNonNull(
  x: ((n: number) => string) | null,
): (n: number) => string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testFunctionWithParamsCall(x: ((n: number) => string) | null): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!(42);
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with unions
///////////////////////////////////////////////////////////////////////////////

function testUnionNonNull(x: number | string | null): number | string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testComplexUnionNonNull(
  x: { a: number } | { b: string } | null,
): { a: number } | { b: string } {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testUnionWithUndefined(
  x: number | string | undefined,
): number | string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testUnionWithBothNullAndUndefined(
  x: number | string | null | undefined,
): number | string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Chained non-null assertions
///////////////////////////////////////////////////////////////////////////////

function testChainedNonNull(x: { field: number | null } | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field!;
}

function testDeeplyChainedNonNull(
  x: { a: { b: { c: number | null } | null } | null } | null,
): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.a!.b!.c!;
}

function testChainedArrayAccess(
  x: (number[] | null)[] | null,
): number[] | null {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0];
}

function testChainedArrayAccess2(
  x: (number[] | null)[] | null,
): number[] | null {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0]!;
}

function testChainedArrayAccessFull(x: (number[] | null)[] | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0]![0];
}

function testChainedArrayAccessFull2(x: (number[] | null)[] | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0]![0]!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with optional properties
///////////////////////////////////////////////////////////////////////////////

function testOptionalPropertyNonNull(x: { field?: number }): {
  field?: number;
} {
  return x;
}

function testOptionalPropertyAccess(x: { field?: number }): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x.field!;
}

function testNestedOptionalPropertyAccess(x: { a?: { b?: number } }): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x.a!.b!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with type aliases
///////////////////////////////////////////////////////////////////////////////

type NullableNumber = number | null;
type NullableString = string | null;

function testTypeAliasNonNull(x: NullableNumber): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testNestedTypeAliasNonNull(
  x: { field: NullableString } | null,
): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with generics
///////////////////////////////////////////////////////////////////////////////

function testGenericNonNull<T>(x: T | null): T {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testGenericNonNullNumber(x: number | null): number {
  return testGenericNonNull<number>(x);
}

function testGenericNonNullString(x: string | null): string {
  return testGenericNonNull<string>(x);
}

function testGenericNonNullWithUndefined<T>(x: T | undefined): T {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testGenericNonNullWithBoth<T>(x: T | null | undefined): T {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions in complex expressions
///////////////////////////////////////////////////////////////////////////////

function testNonNullInBinaryExpression(x: number | null, y: number): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x! + y;
}

function testNonNullInComparison(x: number | null, y: number): boolean {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x! > y;
}

function testNonNullInLogicalExpression(
  x: boolean | null,
  y: boolean,
): boolean {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x! && y;
}

function testNonNullInTernary(
  x: number | null,
  condition: boolean,
): number | string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return condition ? x! : "default";
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with method calls
///////////////////////////////////////////////////////////////////////////////

function testMethodCallNonNull(x: string | null): boolean {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.startsWith("foo");
}

function testChainedMethodCalls(x: string | null): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.toLowerCase().toUpperCase();
}

function testMethodCallOnOptionalProperty(x: { s?: string }): boolean {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x.s!.startsWith("foo");
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with array methods
///////////////////////////////////////////////////////////////////////////////

function testArrayMapNonNull(x: number[] | null): number[] {
  // @skjs-expect-error A parameter must have an explicit type annotation
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.map((n) => n * 2);
}

function testArrayFilterNonNull(x: number[] | null): number[] {
  // @skjs-expect-error A parameter must have an explicit type annotation
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.filter((n) => n > 0);
}

function testArrayReduceNonNull(x: number[] | null): number {
  // @skjs-expect-error A parameter must have an explicit type annotation
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.reduce((acc, n) => acc + n, 0);
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions in assignments
///////////////////////////////////////////////////////////////////////////////

function testAssignmentNonNull(x: number | null): number {
  let y: number;
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  y = x!;
  return y;
}

function testPropertyAssignmentNonNull(x: number | null): { field: number } {
  let obj = { field: 0 };
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  obj.field = x!;
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with return statements
///////////////////////////////////////////////////////////////////////////////

function testReturnNonNull(x: number | null): number {
  if (true) {
    // @skjs-expect-error The non-null assertion operator '!' is not allowed
    return x!;
  }
  return 0;
}

function testMultipleReturnsNonNull(
  x: number | null,
  condition: boolean,
): number {
  if (condition) {
    // @skjs-expect-error The non-null assertion operator '!' is not allowed
    return x!;
  } else {
    // @skjs-expect-error The non-null assertion operator '!' is not allowed
    return x!;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with destructuring
///////////////////////////////////////////////////////////////////////////////

function testDestructuringNonNull(x: { a: number; b: string } | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  const { a } = x!;
  return a;
}

function testNestedDestructuringNonNull(
  x: { a: { b: number } } | null,
): number {
  const {
    a: { b },
    // @skjs-expect-error The non-null assertion operator '!' is not allowed
  } = x!;
  return b;
}

function testArrayDestructuringNonNull(x: number[] | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  const [first] = x!;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return first;
}

function testArrayDestructuringNonNullButUndefined(
  x: number[] | null,
): number | undefined {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  const [first] = x!;
  return first;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with class instances
///////////////////////////////////////////////////////////////////////////////

class TestClass {
  field: number;
  constructor(field: number) {
    this.field = field;
  }
  getField(): number {
    return this.field;
  }
}

function testClassInstanceNonNull(x: TestClass | null): TestClass {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testClassInstanceFieldAccess(x: TestClass | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field;
}

function testClassInstanceMethodCall(x: TestClass | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.getField();
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with interfaces
///////////////////////////////////////////////////////////////////////////////

interface TestInterface {
  field: number;
  method(): string;
}

function testInterfaceNonNull(x: TestInterface | null): TestInterface {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testInterfaceFieldAccess(x: TestInterface | null): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field;
}

function testInterfaceMethodCall(x: TestInterface | null): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.method();
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with algebraic types
///////////////////////////////////////////////////////////////////////////////

type ADT = { kind: "A"; value: number } | { kind: "B"; value: string };

function testADTNonNull(x: ADT | null): ADT {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testADTFieldAccess(x: ADT | null): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.kind;
}

function testADTWithTypeGuard(x: ADT | null): number | string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  if (x!.kind === "A") {
    // FIXME if we're in this branch, then x! succeeded
    // @skjs-expect-error Property access is not allowed on this type
    return x.value;
  } else {
    return x.value;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Multiple non-null assertions in single expression
///////////////////////////////////////////////////////////////////////////////

function testMultipleNonNullsInExpression(
  x: number | null,
  y: number | null,
): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x! + y!;
}

function testMultipleNonNullsWithObjects(
  x: { a: number } | null,
  y: { b: string } | null,
): string {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.a.toString() + y!.b;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with Promise types
///////////////////////////////////////////////////////////////////////////////

function testPromiseNonNull(x: Promise<number> | null): Promise<number> {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

function testPromiseThen(x: Promise<number> | null): Promise<string> {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.then((n: number) => n.toString());
}

///////////////////////////////////////////////////////////////////////////////
// Negative tests - incorrect usage of postfix exclamation mark
// These should error even after the operator is implemented
///////////////////////////////////////////////////////////////////////////////

// Using ! on a value that is never null/undefined
function testNonNullableValue(): number {
  let x: number = 42;
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return x!;
}

// Using ! doesn't change the type incorrectly
function testWrongTypeAfterNonNull(x: string | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! on already non-nullable type in wrong context
function testNonNullOnNonNullable(): string {
  let x: number = 42;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return x!;
}

// Multiple ! doesn't change the type
function testMultipleExclamations(x: number | null): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return x!!;
}

// Using ! doesn't convert types
function testNoTypeConversion(x: string | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! on incompatible union after removal of null
function testIncompatibleUnionAfterNonNull(x: string | boolean | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! doesn't make optional property required
function testOptionalPropertyStillOptional(x: { field?: number }): number {
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x.field!;
}

// Wrong field access after non-null assertion
function testWrongFieldAccessAfterNonNull(x: { a: number } | null): string {
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.b;
}

// Wrong array element type after non-null assertion
function testWrongArrayElementType(x: number[] | null): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x![0];
}

// Using ! on undefined alone doesn't help with accessing properties
function testUndefinedPropertyAccess(x: { field: number } | undefined): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field;
}

// Chained ! with wrong final type
function testChainedNonNullWrongType(
  x: { field: number | null } | null,
): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.field!;
}

// Using ! in wrong arithmetic context
function testNonNullInWrongArithmetic(x: string | null, y: number): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error Right operand of '+' is not assignable to the left operand's type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x! + y;
}

// Using ! doesn't fix incompatible function signature
function testIncompatibleFunctionAfterNonNull(
  x: ((s: string) => number) | null,
): (n: number) => string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! on wrong generic type
function testWrongGenericAfterNonNull<T>(x: T | null): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! doesn't bypass required type guard
function testTypeGuardStillNeeded(
  x: { kind: "A"; value: number } | { kind: "B"; value: string } | null,
): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.value;
}

// Using ! on method with wrong return type expectation
function testMethodWrongReturnType(x: string | null): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.toLowerCase();
}

// Using ! doesn't make incompatible tuple types compatible
function testIncompatibleTupleAfterNonNull(
  x: [number, string] | null,
): [string, number] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! on class instance with wrong method
function testWrongMethodAfterNonNull(x: TestClass | null): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.getField();
}

// Using ! doesn't fix interface incompatibility
function testInterfaceIncompatibility(x: TestInterface | null): {
  field: string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! in assignment to wrong type
function testAssignmentToWrongType(x: number | null): string {
  let y: string;
  // TODO: Type 'number' is not assignable to type 'string'
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  y = x!;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return y;
}

// Using ! on nested object with wrong path
function testWrongNestedPath(x: { a: { b: number } } | null): string {
  // @skjs-expect-error Property 'c' does not exist on this type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.a.c;
}

// Using ! doesn't allow calling non-function
function testCallingNonFunction(x: number | null): number {
  // @skjs-expect-error This expression is not callable
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!();
}

// Using ! on array with wrong method
function testWrongArrayMethod(x: number[] | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error A parameter must have an explicit type annotation
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!.map((n) => n * 2);
}

// Using ! doesn't fix readonly/mutable mismatch
function testReadonlyMismatch(x: readonly number[] | null): number[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}

// Using ! on promise with wrong generic type
function testWrongPromiseGeneric(x: Promise<number> | null): Promise<string> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
  return x!;
}
