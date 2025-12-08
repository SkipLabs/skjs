// Comprehensive tests for spread operator in function calls
// Tests both positive cases (should work when implemented) and negative cases (should error)

// Helper functions for testing
function takesThreeNumbers(a: number, b: number, c: number): void {}
function takesTwoStrings(a: string, b: string): void {}
function takesNumberAndString(a: number, b: string): void {}
function takesRestNumbers(...args: number[]): void {}
function takesOneAndRest(first: number, ...rest: string[]): void {}
function takesTwoAndRest(a: number, b: string, ...rest: boolean[]): void {}
function takesOptional(a: number, b?: string): void {}
function takesGeneric<T>(a: T, b: T): void {}

// POSITIVE TESTS - Should work when feature is implemented

// Test 1: Basic spread with exact argument count
function testBasicSpread(): void {
  const args: [number, number, number] = [1, 2, 3];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...args);
}

// Test 2: Spread with rest parameters
function testSpreadWithRestParams(): void {
  const nums = new Array<number>();
  nums.push(1);
  nums.push(2);
  // @skjs-expect-error TODO: ...
  takesRestNumbers(...nums);
}

// Test 3: Spread array with matching types
function testSpreadArray(): void {
  const args = new Array<number>();
  args.push(1);
  args.push(2);
  args.push(3);
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...args);
}

// Test 4: Multiple spreads in one call
function testMultipleSpreads(): void {
  const nums1: [number] = [1];
  const nums2: [number, number] = [2, 3];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...nums1, ...nums2);
}

// Test 5: Mixed regular and spread arguments
function testMixedArguments(): void {
  const rest: [number, number] = [2, 3];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(1, ...rest);
}

// Test 6: Spread after regular arguments
function testSpreadAfterRegular(): void {
  const rest = new Array<string>();
  rest.push("hello");
  rest.push("world");
  // @skjs-expect-error TODO: ...
  takesOneAndRest(1, ...rest);
}

// Test 7: Spread with tuple types
function testSpreadTuple(): void {
  const tuple: [number, string] = [42, "hello"];
  // @skjs-expect-error TODO: ...
  takesNumberAndString(...tuple);
}

// Test 8: Empty spread with rest parameters
function testEmptySpread(): void {
  const empty: number[] = new Array<number>();
  // @skjs-expect-error TODO: ...
  takesRestNumbers(...empty);
}

// Test 9: Spread with optional parameters
function testSpreadWithOptional(): void {
  const args: [number, string] = [1, "hello"];
  // @skjs-expect-error TODO: ...
  takesOptional(...args);
}

// Test 10: Spread single element tuple
function testSpreadSingleElement(): void {
  const single: [number] = [42];
  // @skjs-expect-error TODO: ...
  takesOptional(...single);
}

// NEGATIVE TESTS - Should error even when spread is implemented

// Test 11: Wrong argument types in spread
function testWrongTypes(): void {
  const wrongArgs: [string, string, string] = ["a", "b", "c"];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...wrongArgs);
  // TODO: Should also error with "Invalid call" for type mismatch
}

// Test 12: Too few arguments via spread
function testTooFewArguments(): void {
  const tooFew: [number, number] = [1, 2];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...tooFew);
  // TODO: Should also error with "Invalid call" for missing argument
}

// Test 13: Too many arguments (non-rest function)
function testTooManyArguments(): void {
  const tooMany: [number, number, number, number] = [1, 2, 3, 4];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...tooMany);
  // TODO: Should also error with "Invalid call" for extra argument
}

// Test 14: Spread non-array type
function testSpreadNonArray(): void {
  const notArray: number = 42;
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...notArray);
  // TODO: Should also error - cannot spread non-iterable
}

// Test 15: Spread object (not array)
function testSpreadObject(): void {
  const obj: { a: number; b: number; c: number } = { a: 1, b: 2, c: 3 };
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...obj);
  // TODO: Should also error - cannot spread object
}

// Test 16: Mixed types with wrong spread type
function testMixedWrongTypes(): void {
  const wrongRest: [number, number] = [1, 2];
  // @skjs-expect-error TODO: ...
  takesOneAndRest(1, ...wrongRest);
  // TODO: Should also error - expects string[] rest, got number[]
}

// Test 17: Spread with type mismatch in rest
function testRestTypeMismatch(): void {
  const wrongTypes: [number, string, number] = [1, "x", 2];
  // @skjs-expect-error TODO: ...
  takesTwoAndRest(...wrongTypes);
  // TODO: Should also error - third element should be boolean
}

// Test 18: Generic function with spread
function testGenericSpread(): void {
  const args: [number, string] = [1, "hello"];
  // @skjs-expect-error TODO: ...
  takesGeneric(...args);
  // TODO: Should also error - type parameters don't match
}

// Test 19: Spread undefined
function testSpreadUndefined(): void {
  const maybeArgs: [number, number, number] | undefined = undefined;
  let args = maybeArgs ?? [1, 2, 3];
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...args);
}

// Test 20: Spread in constructor call
class MyClass {
  constructor(a: number, b: string) {}
}

function testSpreadInConstructor(): void {
  const args: [number, string] = [42, "hello"];
  // @skjs-expect-error TODO: ...
  const instance = new MyClass(...args);
}

// Test 21: Chained spread calls
function returnsArray(): [number, number, number] {
  return [1, 2, 3];
}

function testChainedSpreadCalls(): void {
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...returnsArray());
}

// Test 22: Spread with array methods
function testSpreadWithArrayMethods(): void {
  const arr = new Array<number>();
  arr.push(1);
  arr.push(2);
  arr.push(3);
  // @skjs-expect-error TODO: ...
  takesThreeNumbers(...arr);
}
