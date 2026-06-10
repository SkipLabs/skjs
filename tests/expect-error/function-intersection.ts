// Comprehensive tests for function intersection types
// Intersection of functions: ((a: T1) => R1) & ((a: T2) => R2)

// Type hierarchy for testing
type Animal = { name: string };
type Dog = { name: string; breed: string };
type Cat = { name: string; meow: () => void };

// Type aliases for intersections (must be at module level)
type SameSignatureInter = ((x: number) => string) & ((x: number) => string);
type SubtypeInter = ((x: number) => Dog) & ((x: number) => Animal);
type DifferentReturnTypesInter = ((x: number) => string) &
  ((x: number) => boolean);
type DifferentParamTypesInter = ((x: number) => string) &
  ((x: string) => string);
type DifferentParamCountsInter = ((a: number) => string) &
  ((a: number, b: string) => string);
type OptionalParamInter = ((a: number, b?: string) => string) &
  ((a: number) => string);
type RestParamInter = ((a: number, ...rest: string[]) => string) &
  ((a: number) => string);
type ParamContravarianceInter = ((a: Animal) => string) & ((a: Dog) => string);
type ReturnCovarianceInter = ((a: number) => Dog) & ((a: number) => Animal);
type TripleInter = ((x: number) => string) &
  ((x: number) => boolean) &
  ((x: number) => number);
type IntersectionWithVoid = ((x: number) => void) & ((x: number) => string);
type F1 = (x: number) => string;
type F2 = (x: number) => boolean;
type InterF1F2 = F1 & F2;
type IntersectionWithNever = ((x: number) => string) & never;
type IntersectionDifferentArities = (() => string) & ((x: number) => string);
type IntersectionIncompatible1 = ((x: number) => string) &
  ((x: boolean) => string);
type IntersectionIncompatible2 = ((x: number) => string) &
  ((x: number) => boolean);
type IntersectionIncompatible3 = ((x: Dog) => string) & ((x: Cat) => string);
type Inter1 = ((x: number) => string) & ((x: number) => boolean);
type Inter2 = ((x: number) => string) & ((x: number) => boolean);
type UnionOfInters = Inter1 | Inter2;
type Inner1 = ((x: number) => string) & ((x: number) => boolean);
type Outer1 = (fn: Inner1) => void;
type Outer2 = (fn: (x: number) => string) => void;
type NestedInter = Outer1 & Outer2;
type PreservesVarianceInter = ((x: Animal) => Dog) & ((x: Animal) => Animal);
type WrongVarianceInter = ((x: Dog) => Animal) & ((x: Cat) => Animal);

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

function withOptional(_a: number, _b?: string): string {
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

// BASIC INTERSECTION TESTS

// Test 1: Intersection of identical function types
function testSameSignatureIntersection(): void {
  const inter: SameSignatureInter = returnString;
}

// Test 2: Intersection where one is subtype of other (return covariance)
function testSubtypeIntersection(): void {
  const inter: SubtypeInter = returnDog;
}

// Test 3: Intersection with different incompatible return types should be empty
function testDifferentReturnTypes(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: DifferentReturnTypesInter = returnString;
}

// Test 4: Intersection with different parameter types should be empty
function testDifferentParamTypes(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: DifferentParamTypesInter = returnString;
}

// PARAMETER COUNT TESTS

// Test 5: Intersection with different parameter counts - result is more specific (2 params)
function testDifferentParamCounts(): void {
  const inter1: DifferentParamCountsInter = returnString;
}

// Test 6: Can assign function with more params to intersection
function testMoreParamsToIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: DifferentParamCountsInter = twoParamsStrings;
}

// OPTIONAL PARAMETER TESTS

// Test 7: Intersection with optional parameters
function testOptionalParamIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter1: OptionalParamInter = withOptional;
}

// Test 8: Assign function without optional to intersection - works due to subtyping
function testNoOptionalToIntersection(): void {
  const inter: OptionalParamInter = returnString;
}

// REST PARAMETER TESTS

// Test 9: Intersection with rest parameters
function testRestParamIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter1: RestParamInter = withRest;
}

// Test 10: Assign function without rest to intersection - works due to subtyping
function testNoRestToIntersection(): void {
  const inter: RestParamInter = returnString;
}

// VARIANCE TESTS

// Test 11: Parameter contravariance - intersection takes less specific param (Animal)
function testParamContravarianceIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: ParamContravarianceInter = acceptDog;
}

// Test 12: Can assign less specific param type - intersection already takes Animal
function testCannotAssignLessSpecificParam(): void {
  const inter: ParamContravarianceInter = acceptAnimal;
}

// Test 13: Return type covariance in intersection
function testReturnCovarianceIntersection(): void {
  const inter: ReturnCovarianceInter = returnDog;
}

// Test 14: Cannot assign less specific return type to intersection
function testCannotAssignLessSpecificReturn(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: ReturnCovarianceInter = returnAnimalType;
}

// COMPLEX INTERSECTION TESTS

// Test 15: Triple intersection with incompatible return types
function testTripleIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: TripleInter = returnString;
}

// Test 16: Intersection in object property
type ObjWithIntersection = {
  fn: ((x: number) => string) & ((x: number) => string);
};

function testIntersectionInObject(): void {
  const obj: ObjWithIntersection = {
    fn: returnString,
  };
}

// Test 17: Intersection with void return
function testIntersectionWithVoid(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionWithVoid = returnsVoid;
}

// Test 18: Intersection with void should be empty
function testIntersectionWithVoidEmpty(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionWithVoid = returnString;
}

// ASSIGNABILITY TESTS

// Test 19: Intersection of incompatible return types is never
function testCannotExtractBranch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: InterF1F2 = returnString;
  const f1: F1 = inter;
}

// Test 20: Intersection with never is never - can't assign to never
function testIntersectionWithNever(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionWithNever = returnString;
}

// Test 21: Intersection of functions with different arities is empty
function f0(): string {
  return "hello";
}

function testIntersectionDifferentArities1(): void {
  const inter: IntersectionDifferentArities = f0;
}

function testIntersectionDifferentArities2(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionDifferentArities = returnString;
}

// NEGATIVE TESTS

// Test 22: Incompatible parameter types
function wrongFn1(_x: string): string {
  return "wrong";
}

function testIncompatibleParamTypes(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionIncompatible1 = wrongFn1;
}

// Test 23: Incompatible return types
function wrongReturn(_x: number): number {
  return 42;
}

function testIncompatibleReturnTypes(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionIncompatible2 = wrongReturn;
}

// Test 24: Incompatible parameter types (Dog vs Cat)
function wrongParam(_x: Animal): string {
  return "animal";
}

function testIncompatibleDogCat(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: IntersectionIncompatible3 = wrongParam;
}

// Test 25: Union of intersections
function testUnionOfIntersections(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const union: UnionOfInters = returnString;
}

// Test 26: Nested intersection in parameters
function f1Nested(_fn: Inner1): void {}

function testNestedIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: NestedInter = f1Nested;
}

// Test 27: Intersection preserves return type covariance
function returnDogFromAnimal(_a: Animal): Dog {
  return { name: "Fido", breed: "Lab" };
}

function testIntersectionPreservesCovariance(): void {
  const inter: PreservesVarianceInter = returnDogFromAnimal;
  const result: Dog = inter({ name: "test" });
}

// Test 28: Wrong variance in intersection parameters
function wrongFn2(_x: Dog): Animal {
  return { name: "Generic" };
}

function testWrongVarianceInIntersection(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inter: WrongVarianceInter = wrongFn2;
}

// Test 29: Calling intersection requires satisfying both types
function testCallingIntersection(): void {
  const f: ((x: number) => Dog) & ((x: number) => Animal) = returnDog;
  const result: Dog = f(42);
}

// Test 30: Result of intersection is more specific type (Dog & Animal = Dog)
function testIntersectionReturnType(): void {
  const f: ((x: number) => Dog) & ((x: number) => Animal) = returnDog;
  const result: Animal = f(42);
}
