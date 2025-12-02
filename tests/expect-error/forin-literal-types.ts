// Test for...in with literal types

// Literal number types are not allowed
function testNumLiteral(): void {
  const num = 5;
  // @skjs-expect-error for-in loop requires an object or array type
  for (const k in num) {
  }
}

// Literal string types are not allowed
function testStrLiteral(): void {
  const str = "hello";
  // @skjs-expect-error for-in loop requires an object or array type
  for (const k in str) {
  }
}

// Objects are allowed
function testObj(): void {
  const obj = { a: 1, b: 2 };
  for (const k in obj) {
  }
}

// Tuples are allowed
function testTuples(): void {
  const arr = [1, 2, 3];
  for (const k in arr) {
  }
}
