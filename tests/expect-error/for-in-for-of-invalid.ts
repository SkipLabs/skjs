// Invalid for-in and for-of loop tests - these should produce type errors

function testForInWithPrimitive(): void {
  const num = 42;
  // @ts-expect-error for-in loop requires an object or array type
  for (const key in num) {
  }
}

function testForOfWithPrimitive(): void {
  const str = "hello";
  for (const char of str) {
    console.log(char);
  }
}

function testForInWrongVariableType(): void {
  const obj = { a: 1, b: 2 };
  for (const key in obj) {
    // @ts-expect-error Invalid annotation
    const n: number = key; // string not assignable to number
  }
}

function testForOfWrongVariableType(): void {
  const arr = [1, 2, 3];
  for (const value of arr) {
    // @ts-expect-error Invalid annotation
    const s: string = value; // number not assignable to string
  }
}

function testForInWithNull(): void {
  const nullObj = null;
  // @ts-expect-error for-in loop requires an object or array type
  for (const key in nullObj) {
  }
}

function testForOfWithUndefined(): void {
  const undefinedArr = undefined;
  // @ts-expect-error for-of loop requires an array, string, or iterable type
  for (const value of undefinedArr) {
  }
}
