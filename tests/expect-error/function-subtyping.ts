// Comprehensive tests for function subtyping
// Tests parameter contravariance, return type covariance, optional parameters, etc.

// Type hierarchy for testing
type Animal = { name: string };
type Dog = { name: string; breed: string };
type Cat = { name: string; meow: () => void };

// RETURN TYPE COVARIANCE TESTS
// A function returning a more specific type is a subtype of one returning a more general type

// Test 1: Return type covariance - basic
function testReturnCovariance(): void {
  const returnsDog: () => Dog = () => ({ name: "Fido", breed: "Lab" });
  const acceptsAnimalReturner: () => Animal = returnsDog;
}

// Test 2: Return type covariance - with parameters
function testReturnCovarianceWithParams(): void {
  const returnsDog: (x: number) => Dog = (_x: number) => ({
    name: "Fido",
    breed: "Lab",
  });
  const acceptsAnimalReturner: (x: number) => Animal = returnsDog;
}

// Test 3: Return type contravariance fails (negative test)
function testReturnContravarianceFails(): void {
  const returnsAnimal: () => Animal = () => ({ name: "Generic" });
  // @skjs-expect-error Invalid annotation
  const acceptsDogReturner: () => Dog = returnsAnimal;
}

// PARAMETER CONTRAVARIANCE TESTS
// A function accepting a more general type is a subtype of one accepting a more specific type

// Test 4: Parameter contravariance - basic
function testParamContravariance(): void {
  const acceptsAnimal: (a: Animal) => void = (_a: Animal) => {};
  const needsDogAcceptor: (d: Dog) => void = acceptsAnimal;
}

// Test 5: Parameter contravariance - multiple parameters
function testParamContravarianceMultiple(): void {
  const acceptsAnimals: (a: Animal, b: Animal) => void = (
    _a: Animal,
    _b: Animal,
  ) => {};
  const needsDogAcceptors: (a: Dog, b: Dog) => void = acceptsAnimals;
}

// Test 6: Parameter covariance fails (negative test)
function testParamCovarianceFails(): void {
  const acceptsDog: (d: Dog) => void = (_d: Dog) => {};
  // @skjs-expect-error Invalid annotation
  const needsAnimalAcceptor: (a: Animal) => void = acceptsDog;
}

// Test 7: Mixed variance - params contravariant, return covariant
function testMixedVariance(): void {
  const fn: (a: Animal) => Dog = (_a: Animal) => ({
    name: "Fido",
    breed: "Lab",
  });
  const target: (d: Dog) => Animal = fn;
}

// PARAMETER COUNT TESTS

// Test 8: Fewer parameters is subtype (extra params ignored)
function testFewerParamsIsSubtype(): void {
  const oneParam: (a: number) => void = (_a: number) => {};
  // FIXME: Should allow function with fewer params to be assigned to one with more params
  // @skjs-expect-error Invalid annotation
  const acceptsTwoParams: (a: number, b: string) => void = oneParam;
}

// Test 9: More required params fails (negative test)
function testMoreRequiredParamsFails(): void {
  const twoParams: (a: number, b: string) => void = (
    _a: number,
    _b: string,
  ) => {};
  // @skjs-expect-error Invalid annotation
  const acceptsOneParam: (a: number) => void = twoParams;
}

// OPTIONAL PARAMETER TESTS

// Test 10: Required param for optional fails (negative test)
function testRequiredForOptional(): void {
  const twoRequired: (a: number, b: string) => void = (
    _a: number,
    _b: string,
  ) => {};
  // @skjs-expect-error Invalid annotation
  const targetOneRequiredOneOptional: (a: number, b?: string) => void =
    twoRequired;
}

// Test 11: Fewer params works with optional target params
function testFewerParamsWithOptional(): void {
  const oneParam: (a: number) => void = (_a: number) => {};
  const acceptsOptionalSecond: (a: number, b?: string) => void = oneParam;
}

// Test 12: Optional param for required fails (negative test)
function testOptionalForRequiredFails(): void {
  const oneRequiredOneOptional: (a: number, b?: string) => void = (
    _a: number,
  ) => {};
  // @skjs-expect-error Invalid annotation
  const acceptsTwoRequired: (a: number, b: string) => void =
    oneRequiredOneOptional;
}

// REST PARAMETER TESTS

// Test 13: Rest parameter compatibility
function withRestHelper(_a: number, ..._rest: string[]): void {}
function testRestParameter(): void {
  const acceptsRest: (a: number, ...rest: string[]) => void = withRestHelper;
}

// Test 14: Missing rest fails (negative test)
function noRestHelper(_a: number): void {}
function testMissingRestFails(): void {
  // @skjs-expect-error Invalid annotation
  const acceptsRest: (a: number, ...rest: string[]) => void = noRestHelper;
}

// Test 15: Rest parameter type contravariance
function acceptsAnimalsHelper(..._animals: Animal[]): void {}
function testRestContravariance(): void {
  // FIXME: Should allow rest parameter contravariance - Dog[] args can be passed to ...Animal[]
  // @skjs-expect-error Invalid annotation
  const needsDogs: (...dogs: Dog[]) => void = acceptsAnimalsHelper;
}

// VOID RETURN TYPE TESTS

// Test 16: Non-void to void should be allowed (TypeScript allows this)
function testNonVoidToVoid(): void {
  const returnsNumber: () => number = () => 42;
  // FIXME: Should allow assigning function returning T to function returning void (return value discarded)
  // @skjs-expect-error Invalid annotation
  const acceptsVoid: () => void = returnsNumber;
}

// Test 17: Void to non-void fails (negative test)
function testVoidToNonVoidFails(): void {
  const returnsVoid: () => void = () => {};
  // @skjs-expect-error Invalid annotation
  const acceptsNumber: () => number = returnsVoid;
}

// UNION TYPE TESTS

// Test 18: Specific type to union
function testSpecificToUnion(): void {
  const returnsNumber: () => number = () => 42;
  const acceptsUnion: () => number | string = returnsNumber;
}

// Test 19: Union to specific fails (negative test)
function testUnionToSpecificFails(): void {
  const returnsUnion: () => number | string = () => 42;
  // @skjs-expect-error Invalid annotation
  const acceptsNumber: () => number = returnsUnion;
}

// Test 20: Union param (contravariant)
function testUnionParam(): void {
  const acceptsUnion: (x: number | string) => void = (
    _x: number | string,
  ) => {};
  const needsNumber: (x: number) => void = acceptsUnion;
}

// BIVARIANCE AND EDGE CASES

// Test 21: Same function type
function testSameFunctionType(): void {
  const fn: (a: number) => string = (_a: number) => "hello";
  const same: (a: number) => string = fn;
}

// Test 22: Identity function
function testIdentityFunction(): void {
  const identity: (x: number) => number = (x: number) => x;
  const target: (x: number) => number = identity;
}

// Test 23: Function with no parameters
function testNoParameters(): void {
  const noParams: () => number = () => 42;
  const target: () => number = noParams;
}

// Test 24: Multiple variance checks together
function testMultipleVariance(): void {
  const fn: (a: Animal, b: Animal) => Dog = (_a: Animal, _b: Animal) => ({
    name: "Fido",
    breed: "Lab",
  });
  const target: (a: Dog, b: Cat) => Animal = fn;
}

// COMPLEX TYPE TESTS

// Test 25: Function type in object (covariance + contravariance)
function testFunctionInObject(): void {
  const obj1: { fn: (a: Animal) => Dog } = {
    fn: (_a: Animal) => ({ name: "Fido", breed: "Lab" }),
  };
  const obj2: { fn: (d: Dog) => Animal } = obj1;
}

// Test 26: Higher-order function (parameter contravariance in callback)
function testHigherOrderFunction(): void {
  const hof: (f: (a: Animal) => Dog) => number = (_f: (a: Animal) => Dog) => 42;
  // @skjs-expect-error Invalid annotation
  const target: (f: (d: Dog) => Animal) => number = hof;
}

// Test 27: Callback parameter
function testCallbackParameter(): void {
  const takesCallback: (cb: (x: number) => void) => void = (
    _cb: (x: number) => void,
  ) => {};
  const target: (cb: (x: number) => void) => void = takesCallback;
}
