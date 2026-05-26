// Types for tests 6-7 (must be at top level, not inside functions)
type WithNew = { new (): { value: number } };
type WithCall = { (): void };

// Test 1: Basic progressive typing (unannotated)
function testBasicGrowth(): void {
  let obj = {};
  obj.x = 5;
  obj.y = "hi";
  const result: { x: number; y: string } = obj;
}

// Test 2: Annotated empty object errors at bindType
function testAnnotatedEmpty(): void {
  // @skjs-expect-error Invalid annotation
  let obj: { x: number } = {};
}

// Test 3: Used before growth (LOUsed)
function testUsedBeforeGrowth(): void {
  let obj = {};
  const ref = obj; // obj becomes LOUsed
  // @skjs-expect-error You are trying to add a field to this object
  obj.x = 5;
}

// Test 4A: Growth in loop - object declared inside loop
function testGrowthInsideLoop(): void {
  for (let i = 0; i < 10; i++) {
    let obj = {};
    obj.x = i; // Check if this is allowed
  }
}

// Test 4B: Growth in loop - object declared before loop
function testGrowthBeforeLoop(): void {
  let obj = {};
  for (let i = 0; i < 10; i++) {
    // @skjs-expect-error You cannot add a field to an object in a loop
    obj.x = i;
  }
}

// Test 5: With index signature (field name matches index key type)
function testWithIndexSignature(): void {
  let obj: { [key: string]: number } = {};
  obj.x = 5; // OK: "x" is a subtype of string, so use index signature
}

// Test 5b: Index signature with numeric key (field name doesn't match)
function testWithNumericIndexSignature(): void {
  let obj: { [key: number]: string } = {};
  // @skjs-expect-error Invalid index key: expected number, got string
  obj.x = "hello"; // OK: "x" is NOT a subtype of number, so add as field
  const result: { x: string } = obj;
}

// Test 6: With constructor signature
function testWithConstructor(): void {
  // @skjs-expect-error Invalid annotation
  let obj: WithNew = {};
}

// Test 7: With call signature
function testWithCallSignature(): void {
  // @skjs-expect-error Invalid annotation
  let obj: WithCall = {};
}

// Test 8: Multiple fields added progressively
function testMultipleFields(): void {
  let obj = {};
  obj.a = 1;
  obj.b = "two";
  obj.c = true;
  const result: { a: number; b: string; c: boolean } = obj;
}

// Test 9: Nested object literals (build inner first, then assign)
function testNestedLiterals(): void {
  let inner = {};
  inner.value = 42;
  let outer = {};
  outer.inner = inner;
  const result: { inner: { value: number } } = outer;
}

// Test 10: Return local object from function
function testReturnLocalObject(): { x: number; y: string } {
  let obj = {};
  obj.x = 10;
  obj.y = "hello";
  return obj;
}

// Test 11: Computed key with string variable + index signature (should pass)
function testComputedKeyBroadWithIndex(): void {
  let obj: { [key: string]: number } = {};
  let key: string = "x";
  obj[key] = 42;
}

// Test 12: Computed key with broad type, no index signature — should error
function testComputedKeyBroadNoIndex(): void {
  let obj = {};
  obj.x = 1;
  let key: string = "y";
  // @skjs-expect-error Computed property key must match an index signature on this object
  obj[key] = 2;
}

// Test 13: Computed key with string variable + wrong value type — should error
function testComputedKeyBroadWrongType(): void {
  let obj: { [key: string]: number } = {};
  let key: string = "x";
  // @skjs-expect-error Invalid assignment
  obj[key] = "hello";
}

// Test 14: Multi-literal key grows with optional fields
function testMultiLiteralKey(key: "a" | "b"): void {
  let obj = {};
  obj[key] = 42;
  const result: { a?: number; b?: number } = obj;
}

// Test 15: Growth after spread with index — field should override index
function testGrowthAfterSpreadWithIndex(src: { [key: string]: number }): void {
  let obj = { ...src };
  obj.x = "hello";
}

// TODO: handle growth on the same field with different type, should probably union
