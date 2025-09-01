// Invalid for-in and for-of loop tests - these should produce type errors

function testForInWithPrimitive(): void {
  const num = 42;
  // @ts-expect-error
  for (const key in num) {
    // Should error: for-in loop requires an object or array type
  }
}

function testForOfWithPrimitive(): void {
  const str = "hello";
  // @ts-expect-error
  for (const char of str) {
    // Should error: for-of loop requires an array, object, or iterable type
  }
}

function testForInWrongVariableType(): void {
  const obj = { a: 1, b: 2 };
  for (const key in obj) {
    // @ts-expect-error
    const n: number = key; // Should error: string not assignable to number
  }
}

function testForOfWrongVariableType(): void {
  const arr = [1, 2, 3];
  for (const value of arr) {
    // @ts-expect-error
    const s: string = value; // Should error: number not assignable to string
  }
}

function testForInWithNull(): void {
  const nullObj = null;
  // @ts-expect-error
  for (const key in nullObj) {
    // Should error: for-in loop requires an object or array type
  }
}

function testForOfWithUndefined(): void {
  const undefinedArr = undefined;
  // @ts-expect-error
  for (const value of undefinedArr) {
    // Should error: for-of loop requires an array, object, or iterable type
  }
}
