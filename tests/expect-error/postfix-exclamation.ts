///////////////////////////////////////////////////////////////////////////////
// Tests for postfix exclamation mark (non-null assertion operator)
// FIXME: SKJS does not support the postfix ! operator yet
// All these tests should succeed once the operator is implemented
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic non-null assertions
///////////////////////////////////////////////////////////////////////////////

function testBasicNonNull(x: number | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testBasicNonUndefined(x: number | undefined): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testBasicNonNullOrUndefined(x: number | null | undefined): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testStringNonNull(x: string | null): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testBooleanNonNull(x: boolean | null): boolean {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with objects
///////////////////////////////////////////////////////////////////////////////

function testObjectNonNull(x: { field: number } | null): { field: number } {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testObjectFieldAccess(x: { field: number } | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field;
}

function testNestedObjectNonNull(x: { a: { b: number } } | null): {
  a: { b: number };
} {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testNestedObjectFieldAccess(x: { a: { b: number } } | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.a.b;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with arrays
///////////////////////////////////////////////////////////////////////////////

function testArrayNonNull(x: number[] | null): number[] {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testArrayAccess(x: number[] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0];
}

function testArrayOfObjectsNonNull(
  x: { field: number }[] | null,
): { field: number }[] {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testArrayOfObjectsAccess(x: { field: number }[] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0].field;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with tuples
///////////////////////////////////////////////////////////////////////////////

function testTupleNonNull(x: [number, string] | null): [number, string] {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testTupleAccess(x: [number, string] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0];
}

function testTupleDestructuring(x: [number, string] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  const [n, _s] = x!;
  return n;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with functions
///////////////////////////////////////////////////////////////////////////////

function testFunctionNonNull(x: (() => number) | null): () => number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testFunctionCall(x: (() => number) | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!();
}

function testFunctionWithParamsNonNull(
  x: ((n: number) => string) | null,
): (n: number) => string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testFunctionWithParamsCall(x: ((n: number) => string) | null): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!(42);
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with unions
///////////////////////////////////////////////////////////////////////////////

function testUnionNonNull(x: number | string | null): number | string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testComplexUnionNonNull(
  x: { a: number } | { b: string } | null,
): { a: number } | { b: string } {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testUnionWithUndefined(
  x: number | string | undefined,
): number | string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testUnionWithBothNullAndUndefined(
  x: number | string | null | undefined,
): number | string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Chained non-null assertions
///////////////////////////////////////////////////////////////////////////////

function testChainedNonNull(x: { field: number | null } | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field!;
}

function testDeeplyChainedNonNull(
  x: { a: { b: { c: number | null } | null } | null } | null,
): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.a!.b!.c!;
}

function testChainedArrayAccess(
  x: (number[] | null)[] | null,
): number[] | null {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0];
}

function testChainedArrayAccessFull(x: (number[] | null)[] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0]![0];
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
  // @skjs-expect-error Construction not supported: postfix operator !
  return x.field!;
}

function testNestedOptionalPropertyAccess(x: { a?: { b?: number } }): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x.a!.b!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with type aliases
///////////////////////////////////////////////////////////////////////////////

type NullableNumber = number | null;
type NullableString = string | null;

function testTypeAliasNonNull(x: NullableNumber): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testNestedTypeAliasNonNull(
  x: { field: NullableString } | null,
): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with generics
///////////////////////////////////////////////////////////////////////////////

function testGenericNonNull<T>(x: T | null): T {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testGenericNonNullNumber(x: number | null): number {
  return testGenericNonNull<number>(x);
}

function testGenericNonNullString(x: string | null): string {
  return testGenericNonNull<string>(x);
}

function testGenericNonNullWithUndefined<T>(x: T | undefined): T {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testGenericNonNullWithBoth<T>(x: T | null | undefined): T {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions in complex expressions
///////////////////////////////////////////////////////////////////////////////

function testNonNullInBinaryExpression(x: number | null, y: number): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x! + y;
}

function testNonNullInComparison(x: number | null, y: number): boolean {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x! > y;
}

function testNonNullInLogicalExpression(
  x: boolean | null,
  y: boolean,
): boolean {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x! && y;
}

function testNonNullInTernary(
  x: number | null,
  condition: boolean,
): number | string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return condition ? x! : "default";
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with method calls
///////////////////////////////////////////////////////////////////////////////

function testMethodCallNonNull(x: string | null): boolean {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.startsWith("foo");
}

function testChainedMethodCalls(x: string | null): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.toLowerCase().toUpperCase();
}

function testMethodCallOnOptionalProperty(x: { s?: string }): boolean {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x.s!.startsWith("foo");
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with array methods
///////////////////////////////////////////////////////////////////////////////

function testArrayMapNonNull(x: number[] | null): number[] {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.map((n) => n * 2);
}

function testArrayFilterNonNull(x: number[] | null): number[] {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.filter((n) => n > 0);
}

function testArrayReduceNonNull(x: number[] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.reduce((acc, n) => acc + n, 0);
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions in assignments
///////////////////////////////////////////////////////////////////////////////

function testAssignmentNonNull(x: number | null): number {
  let y: number;
  // @skjs-expect-error Construction not supported: postfix operator !
  y = x!;
  return y;
}

function testPropertyAssignmentNonNull(x: number | null): { field: number } {
  let obj = { field: 0 };
  // @skjs-expect-error Construction not supported: postfix operator !
  obj.field = x!;
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with return statements
///////////////////////////////////////////////////////////////////////////////

function testReturnNonNull(x: number | null): number {
  if (true) {
    // @skjs-expect-error Construction not supported: postfix operator !
    return x!;
  }
  return 0;
}

function testMultipleReturnsNonNull(
  x: number | null,
  condition: boolean,
): number {
  if (condition) {
    // @skjs-expect-error Construction not supported: postfix operator !
    return x!;
  } else {
    return x!;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with destructuring
///////////////////////////////////////////////////////////////////////////////

function testDestructuringNonNull(x: { a: number; b: string } | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  const { a } = x!;
  return a;
}

function testNestedDestructuringNonNull(
  x: { a: { b: number } } | null,
): number {
  const {
    a: { b },
    // @skjs-expect-error Construction not supported: postfix operator !
  } = x!;
  return b;
}

function testArrayDestructuringNonNull(x: number[] | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
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
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testClassInstanceFieldAccess(x: TestClass | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field;
}

function testClassInstanceMethodCall(x: TestClass | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
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
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testInterfaceFieldAccess(x: TestInterface | null): number {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field;
}

function testInterfaceMethodCall(x: TestInterface | null): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.method();
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with algebraic types
///////////////////////////////////////////////////////////////////////////////

type ADT = { kind: "A"; value: number } | { kind: "B"; value: string };

function testADTNonNull(x: ADT | null): ADT {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testADTFieldAccess(x: ADT | null): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.kind;
}

function testADTWithTypeGuard(x: ADT | null): number | string {
  // @skjs-expect-error Construction not supported: postfix operator !
  if (x!.kind === "A") {
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
  // @skjs-expect-error Construction not supported: postfix operator !
  return x! + y!;
}

function testMultipleNonNullsWithObjects(
  x: { a: number } | null,
  y: { b: string } | null,
): string {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.a.toString() + y!.b;
}

///////////////////////////////////////////////////////////////////////////////
// Non-null assertions with Promise types
///////////////////////////////////////////////////////////////////////////////

function testPromiseNonNull(x: Promise<number> | null): Promise<number> {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

function testPromiseThen(x: Promise<number> | null): Promise<string> {
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.then((n) => n.toString());
}

///////////////////////////////////////////////////////////////////////////////
// Negative tests - incorrect usage of postfix exclamation mark
// These should error even after the operator is implemented
///////////////////////////////////////////////////////////////////////////////

// Using ! on a value that is never null/undefined
function testNonNullableValue(): number {
  let x: number = 42;
  // TODO: SKJS should warn about unnecessary non-null assertion
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! doesn't change the type incorrectly
function testWrongTypeAfterNonNull(x: string | null): number {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! on already non-nullable type in wrong context
function testNonNullOnNonNullable(): string {
  let x: number = 42;
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Multiple ! doesn't change the type
function testMultipleExclamations(x: number | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!!;
}

// Using ! doesn't convert types
function testNoTypeConversion(x: string | null): number {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! on incompatible union after removal of null
function testIncompatibleUnionAfterNonNull(x: string | boolean | null): number {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! doesn't make optional property required
function testOptionalPropertyStillOptional(x: { field?: number }): number {
  // TODO: SKJS should error on object possibly undefined
  // @skjs-expect-error Construction not supported: postfix operator !
  return x.field!;
}

// Wrong field access after non-null assertion
function testWrongFieldAccessAfterNonNull(x: { a: number } | null): string {
  // TODO: Property 'b' does not exist
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.b;
}

// Wrong array element type after non-null assertion
function testWrongArrayElementType(x: number[] | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x![0];
}

// Using ! on undefined alone doesn't help with accessing properties
function testUndefinedPropertyAccess(x: { field: number } | undefined): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field;
}

// Chained ! with wrong final type
function testChainedNonNullWrongType(
  x: { field: number | null } | null,
): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.field!;
}

// Using ! in wrong arithmetic context
function testNonNullInWrongArithmetic(x: string | null, y: number): number {
  // TODO: The left-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x! + y;
}

// Using ! doesn't fix incompatible function signature
function testIncompatibleFunctionAfterNonNull(
  x: ((s: string) => number) | null,
): (n: number) => string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! on wrong generic type
function testWrongGenericAfterNonNull<T>(x: T | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! doesn't bypass required type guard
function testTypeGuardStillNeeded(
  x: { kind: "A"; value: number } | { kind: "B"; value: string } | null,
): number {
  // TODO: Property 'value' does not exist on type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.value;
}

// Using ! on method with wrong return type expectation
function testMethodWrongReturnType(x: string | null): number {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.toLowerCase();
}

// Using ! doesn't make incompatible tuple types compatible
function testIncompatibleTupleAfterNonNull(
  x: [number, string] | null,
): [string, number] {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! on class instance with wrong method
function testWrongMethodAfterNonNull(x: TestClass | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.getField();
}

// Using ! doesn't fix interface incompatibility
function testInterfaceIncompatibility(x: TestInterface | null): {
  field: string;
} {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! in assignment to wrong type
function testAssignmentToWrongType(x: number | null): string {
  let y: string;
  // TODO: Type 'number' is not assignable to type 'string'
  // @skjs-expect-error Construction not supported: postfix operator !
  y = x!;
  return y;
}

// Using ! on nested object with wrong path
function testWrongNestedPath(x: { a: { b: number } } | null): string {
  // TODO: Property 'c' does not exist
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.a.c;
}

// Using ! doesn't allow calling non-function
function testCallingNonFunction(x: number | null): number {
  // TODO: This expression is not callable
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!();
}

// Using ! on array with wrong method
function testWrongArrayMethod(x: number[] | null): string {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!.map((n) => n * 2);
}

// Using ! doesn't fix readonly/mutable mismatch
// @skjs-expect-error TODO readonly
function testReadonlyMismatch(x: readonly number[] | null): number[] {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}

// Using ! on promise with wrong generic type
function testWrongPromiseGeneric(x: Promise<number> | null): Promise<string> {
  // TODO: Invalid return type
  // @skjs-expect-error Construction not supported: postfix operator !
  return x!;
}
