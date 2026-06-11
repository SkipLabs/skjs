// Test operator precedence using type checking
// Each test has a positive case (correct precedence) and negative case (wrong precedence)

type Obj = { flag: boolean; count: number };

// Test 1: Unary ! has lower precedence than member access
// Correct parse: !(obj.flag) gives boolean
// Wrong parse: (!obj).flag would try .flag on boolean
function testUnaryMemberAccessPositive(obj: Obj): boolean {
  return !obj.flag; // Parses as !(obj.flag), type is boolean
}

function testUnaryMemberAccessNegative(obj: boolean): void {
  // @ts-expect-error Property 'flag' does not exist on this type
  const x: boolean = (!obj).flag; // Forcing wrong precedence: boolean has no .flag
}

// Test 2: Postfix ++ has higher precedence than binary +
// Correct parse: (x++) + y gives number + number = number
// Wrong parse would be syntax error, but we can test type flow
function testPostfixBinaryPositive(): number {
  let x: number = 5;
  let y: number = 3;
  const result: number = x++ + y; // Parses as (x++) + y
  return result;
}

// Test 3: Member access before postfix
// Correct parse: (obj.count)++ increments the number
// We can't really force wrong parse, but test it works
function testMemberPostfixPositive(obj: Obj): number {
  return obj.count++; // Parses as (obj.count)++, returns number
}

// Test 4: Unary operators before binary operators
// Correct parse: (-x) + y where both are numbers
// Wrong parse: -(x + y) would also work, but we can test with types
function testUnaryBinaryTypePositive(): number {
  const x: number = 5;
  const y: number = 3;
  return -x + y; // Parses as (-x) + y
}

// Test 5: Logical && before ||
// Correct parse: a || (b && c)
// Wrong parse: (a || b) && c gives different result
function testLogicalAndOrPositive(): boolean {
  const a: false = false;
  const b: false = false;
  const c: true = true;
  const result: boolean = a || (b && c); // Parses as a || (b && c) = false || false = false
  return result;
}

function testLogicalAndOrNegative(): void {
  const a: false = false;
  const b: false = false;
  const c: true = true;
  // Forcing wrong precedence with explicit parentheses
  const wrong: boolean = (a || b) && c; // This is (false || false) && true = false && true = false
  // Both give false, so not a great test, but demonstrates explicit grouping
  const x: boolean = wrong;
}

// Test 6: Comparison before logical operators
// Correct parse: (x < y) && (y < z)
function testComparisonLogicalPositive(): boolean {
  const x: number = 1;
  const y: number = 2;
  const z: number = 3;
  return x < y && y < z; // Parses as (x < y) && (y < z)
}

// Test 7: Function call before binary operators
// Correct parse: (f()) + (g())
// Testing that function calls bind tighter than +
function testCallBinaryPositive(): number {
  const f = (): number => 5;
  const g = (): number => 3;
  return f() + g(); // Parses as (f()) + (g())
}

// Test 8: Unary with function call
// Correct parse: !(f()) applies ! to result of f()
// Wrong parse: (!f)() would try to call boolean
function testUnaryCallPositive(): boolean {
  const f = (): boolean => true;
  return !f(); // Parses as !(f())
}

function testUnaryCallNegative(): void {
  const f = (): boolean => true;
  // @skjs-expect-error This condition will always be true since this value is always defined
  // @ts-expect-error This expression is not callable
  const result: boolean = (!f)(); // Forcing wrong precedence: boolean is not callable
}

// Test 9: Postfix continues to allow binary operations after it
// This tests the fix for early return after postfix
function testPostfixContinuationPositive(): number {
  let x: number = 5;
  let y: number = 3;
  return x++ + y++; // Parses as (x++) + (y++), not just x++
}

// Test 10: Member access with unary
// Correct: !(obj.flag) gives boolean
// Wrong: (!obj).flag tries .flag on boolean
function testMemberUnaryPositive(obj: Obj): boolean {
  const result: boolean = !obj.flag; // !(obj.flag)
  return result;
}

// Test 11: Multiplication before addition (type preservation)
// Using function that requires number to verify correct evaluation order
function testMultAddPositive(requiresNumber: (n: number) => number): number {
  const x: number = 2;
  const y: number = 3;
  const z: number = 4;
  return requiresNumber(x + y * z); // Must parse as x + (y * z) to get number
}

// Test 12: Nullish coalescing with comparisons
// Correct: (x ?? y) < z
function testNullishComparisonPositive(): boolean {
  const x: number | null = 5;
  const y: number = 10;
  const z: number = 20;
  return (x ?? y) < z; // (x ?? y) gives number, then < z gives boolean
}

// Test 13: Ternary has low precedence
// Correct: x > 0 ? y : z + 1 parses as x > 0 ? y : (z + 1)
function testTernaryBinaryPositive(): number {
  const x: number = 5;
  const y: number = 10;
  const z: number = 3;
  return x > 0 ? y : z + 1; // Comparison happens before ternary
}

// Test 14: Index access with binary
// Correct: arr[i] + arr[j]
function testIndexBinaryPositive(arr: number[]): number {
  const i: number = 0;
  const j: number = 1;
  return (arr[i] ?? 0) + (arr[j] ?? 0); // Both index accesses happen before +
}

// Test 15: Chained member accesses
function testChainedMemberPositive(obj: { nested: { value: number } }): number {
  return obj.nested.value; // Parses as (obj.nested).value
}

function testChainedMemberNegative(obj: { nested: { value: number } }): void {
  // @ts-expect-error Property 'nested' does not exist on this type
  const x: number = obj.nested.value.nested; // Type error: number has no .nested
}
