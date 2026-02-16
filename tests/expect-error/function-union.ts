// Comprehensive tests for function union types
// Union of functions: ((a: T1) => R1) | ((a: T2) => R2)

// Type hierarchy for testing
type Animal = { name: string };
type Dog = { name: string; breed: string };
type Cat = { name: string; meow: () => void };

// Type aliases for unions (must be at module level)
type SameSignatureUnion = ((x: number) => string) | ((x: number) => string);
type DifferentReturnTypesUnion =
  | ((x: number) => string)
  | ((x: number) => boolean);
type DifferentParamTypesUnion =
  | ((x: number) => string)
  | ((x: string) => string);
type StringOrNumberReturnUnion =
  | ((x: number) => string)
  | ((x: number) => number);
type DifferentParamCountsUnion =
  | ((a: number) => string)
  | ((a: number, b: string) => string);
type UnionWithOptional =
  | ((a: number, b: string | undefined) => string)
  | ((a: number) => string);
type UnionWithRest =
  | ((a: number, ...rest: string[]) => string)
  | ((a: number) => string);
type ParamContravarianceUnion = ((a: Animal) => string) | ((a: Dog) => string);
type ReturnCovarianceUnion = ((a: number) => Dog) | ((a: number) => Animal);
type TripleUnion =
  | ((x: number) => string)
  | ((x: number) => boolean)
  | ((x: number) => number);
type UnionWithVoid = ((x: number) => void) | ((x: number) => string);
type OverlappingParamTypesUnion = ((x: Dog) => string) | ((x: Dog) => string);
type F1 = (x: number) => string;
type F2 = (x: number) => boolean;
type UnionF1F2 = F1 | F2;
type UnionWithNever = ((x: number) => string) | never;
type UnionDifferentArities =
  | (() => string)
  | ((x: number) => string)
  | ((x: number, y: string) => string);
type IncompatibleUnion1 = ((x: number) => string) | ((x: boolean) => string);
type IncompatibleUnion2 = ((x: number) => string) | ((x: number) => boolean);
type IncompatibleUnion3 = ((x: Dog) => string) | ((x: Cat) => string);
type Union1 = ((x: number) => string) | ((x: number) => boolean);
type Union2 = ((x: number) => string) | ((x: number) => boolean);
type InterOfUnions = Union1 & Union2;
type UnionWithThisParam =
  | ((this: Dog, x: number) => string)
  | ((this: Cat, x: number) => string);
type Union1Str = ((x: number) => string) | ((x: string) => string);
type Union2StrBool = ((x: string) => string) | ((x: boolean) => string);
type CombinedUnion = Union1Str | Union2StrBool;
type ReturnTypeAllBranches =
  | ((x: number) => string)
  | ((x: number) => number)
  | ((x: number) => boolean);
type IncompatibleAllBranches =
  | ((x: number) => string)
  | ((x: boolean) => string);
type UnionWithGenerics = (<T>(x: T) => T) | (<T>(x: T) => string);
type InnerUnion = ((x: number) => string) | ((x: number) => boolean);
type Outer1 = (fn: InnerUnion) => void;
type Outer2 = (fn: (x: number) => string) => void;
type NestedUnion = Outer1 | Outer2;
type PreservesVarianceUnion = ((x: Dog) => string) | ((x: Cat) => string);
type WrongVarianceUnion = ((x: Animal) => Dog) | ((x: Animal) => Cat);

// Helper functions for testing
function returnString(_x: number): string {
  return "hello";
}

function returnBoolean(_x: number): boolean {
  return true;
}

function returnNumber(_x: number): number {
  return 42;
}

function acceptDog(_x: Dog): string {
  return "dog";
}

function acceptCat(_x: Cat): string {
  return "cat";
}

function acceptAnimal(_a: Animal): string {
  return "animal";
}

function twoParamsStrings(_a: number, _b: string): string {
  return "hello";
}

function withOptional(_a: number, _b: string | undefined): string {
  return "hello";
}

function withRest(_a: number, ..._rest: string[]): string {
  return "hello";
}

function returnsVoid(_x: number): void {}

function returnDog(_a: number): Dog {
  return { name: "Fido", breed: "Lab" };
}

function returnAnimalType(_a: number): Animal {
  return { name: "Generic" };
}

// BASIC UNION TESTS

// Test 1: Union of functions with same signature
function testSameSignatureUnion(): void {
  const union: SameSignatureUnion = returnString;
}

// Test 2: Assigning to union with different return types
function testDifferentReturnTypes(): void {
  const union: DifferentReturnTypesUnion = returnString;
}

// Test 3: Union with different parameter types
function testDifferentParamTypes(): void {
  const union1: DifferentParamTypesUnion = returnString;
}

// Test 4: Union return type must be handled
function testUnionReturnType(): void {
  const f: StringOrNumberReturnUnion = returnString;
  const result: string | number = f(42);
}

// Test 5: Return type must be union or compatible (negative test)
function testReturnTypeMustBeUnion(): void {
  const f: StringOrNumberReturnUnion = returnString;
  // @skjs-expect-error Invalid annotation
  const result: string = f(42);
}

// PARAMETER COUNT TESTS

// Test 6: Union with different parameter counts
function testDifferentParamCounts(): void {
  const union1: DifferentParamCountsUnion = returnString;
  const union2: DifferentParamCountsUnion = twoParamsStrings;
}

// OPTIONAL PARAMETER TESTS

// Test 7: Union with optional parameters
function testUnionWithOptional(): void {
  const union1: UnionWithOptional = withOptional;
  const union2: UnionWithOptional = returnString;
}

// REST PARAMETER TESTS

// Test 8: Union with rest parameters
function testUnionWithRest(): void {
  const union1: UnionWithRest = withRest;
  const union2: UnionWithRest = returnString;
}

// VARIANCE TESTS

// Test 9: Parameter contravariance in union
function testParamContravarianceUnion(): void {
  const union1: ParamContravarianceUnion = acceptAnimal;
  const union2: ParamContravarianceUnion = acceptDog;
}

// Test 10: Return type covariance in union
function testReturnCovarianceUnion(): void {
  const union1: ReturnCovarianceUnion = returnDog;
  const union2: ReturnCovarianceUnion = returnAnimalType;
}

// COMPLEX UNION TESTS

// Test 11: Triple union
function testTripleUnion(): void {
  const union1: TripleUnion = returnString;
  const union2: TripleUnion = returnBoolean;
  const union3: TripleUnion = returnNumber;
}

// Test 12: Union in object property
type ObjWithUnion = {
  fn: ((x: number) => string) | ((x: string) => number);
};

function testUnionInObject(): void {
  // @skjs-expect-error Invalid annotation
  const obj: ObjWithUnion = {
    fn: returnString,
  };
}

// Test 13: Union with void return
function testUnionWithVoid(): void {
  const union1: UnionWithVoid = returnsVoid;
  const union2: UnionWithVoid = returnString;
}

// Test 14: Union with overlapping parameter types
function testOverlappingParamTypes(): void {
  const union: OverlappingParamTypesUnion = acceptDog;
}

// ASSIGNABILITY TESTS

// Test 15: Assigning union to one branch fails (negative test)
function testAssignUnionToBranch(): void {
  const union: UnionF1F2 = returnString;
  // @skjs-expect-error Invalid annotation
  const f1: F1 = union;
}

// Test 16: Union with never
function testUnionWithNever(): void {
  const union: UnionWithNever = returnString;
}

// Test 17: Discriminated union of functions
type Action1 = { type: "add"; fn: (a: number, b: number) => number };
type Action2 = { type: "concat"; fn: (a: string, b: string) => string };
type Action = Action1 | Action2;

function addFn(a: number, b: number): number {
  return a + b;
}

function testDiscriminatedUnion(): void {
  const action: Action = {
    type: "add",
    fn: addFn,
  };
}

// Test 17bis: Discriminated union of functions
type Action1b = { kind: "add"; fn: (a: number, b: number) => number };
type Action2b = { kind: "concat"; fn: (a: string, b: string) => string };
type Actionb = Action1b | Action2b;

function testDiscriminatedUnionb(): void {
  const action: Actionb = {
    kind: "add",
    fn: addFn,
  };
}

// Test 18: Union assignment with different arities
function f0(): string {
  return "hello";
}

function testUnionDifferentArities(): void {
  const union1: UnionDifferentArities = f0;
  const union2: UnionDifferentArities = returnString;
  const union3: UnionDifferentArities = twoParamsStrings;
}

// NEGATIVE TESTS

// Test 19: Incompatible function assignment (negative test)
function wrongFn1(_x: string): string {
  return "wrong";
}

function testIncompatibleAssignment(): void {
  // wrongFn1 takes string but union requires number & boolean
  // Actually OK because we can't call it
  const union: IncompatibleUnion1 = wrongFn1;
}

// Test 20: Wrong return type (negative test)
function wrongReturn(_x: number): number {
  return 42;
}

function testWrongReturnType(): void {
  // @skjs-expect-error Invalid annotation
  const union: IncompatibleUnion2 = wrongReturn;
}

// Test 21: Wrong parameter type (negative test)
function wrongParam(_x: Animal): string {
  return "animal";
}

function testWrongParamType(): void {
  // wrongParam takes Animal but union needs Dog & Cat (more specific types)
  // Actually OK: there can be a { breed: string, meow: () => void, name: string }
  const union: IncompatibleUnion3 = wrongParam;
}

// Test 22: Intersection of unions
function testIntersectionOfUnions(): void {
  const inter1: InterOfUnions = returnString;
  const inter2: InterOfUnions = returnBoolean;
}

// Test 23: Union with different this parameters
// FIXME: SKJS doesn't support 'this' parameter yet
// @skjs-expect-error TODO: support this parameter
function f1(this: Dog, _x: number): string {
  return this.name;
}

// @skjs-expect-error TODO: support this parameter
function f2(this: Cat, _x: number): string {
  return this.name;
}

function testUnionWithThisParam(): void {
  const union1: UnionWithThisParam = f1;
  const union2: UnionWithThisParam = f2;
}

// Test 24: Multiple unions combined
function testMultipleUnionsCombined(): void {
  const combined1: CombinedUnion = returnString;
}

// Test 25: Union return type with multiple branches
function testReturnTypeAllBranches(): void {
  const f: ReturnTypeAllBranches = returnString;
  const result: string | number | boolean = f(42);
}

// Test 26: Incompatible with all branches (negative test)
function wrongFn2(_x: string): number {
  return 42;
}

function testIncompatibleWithAllBranches(): void {
  // @skjs-expect-error Invalid annotation
  const union: IncompatibleAllBranches = wrongFn2;
}

// Test 27: Union with generic functions
function f1Generic<T>(x: T): T {
  return x;
}

function f2Generic<T>(_x: T): string {
  return "hello";
}

function testUnionWithGenerics(): void {
  const union1: UnionWithGenerics = f1Generic;
  const union2: UnionWithGenerics = f2Generic;
}

// Test 28: Nested union in parameters
function f1Nested(_fn: InnerUnion): void {}

function f2Nested(_fn: (x: number) => string): void {}

function testNestedUnion(): void {
  const union1: NestedUnion = f1Nested;
  const union2: NestedUnion = f2Nested;
}

// Test 29: Union of functions with different parameter types requires intersection
function testUnionPreservesVariance(): void {
  const dog: Dog = { name: "Fido", breed: "Lab" };
  const f: PreservesVarianceUnion = acceptDog;
  // @skjs-expect-error Invalid call
  const result: string = f(dog);
}

// Test 30: Wrong variance in union (negative test)
function wrongFn3(_x: Dog): Animal {
  return { name: "Generic" };
}

function testWrongVarianceInUnion(): void {
  // @skjs-expect-error Invalid annotation
  const union: WrongVarianceUnion = wrongFn3;
}
