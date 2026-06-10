// Invalid for-in and for-of loop tests - these should produce type errors

function testForInWithPrimitive(): void {
  const num = 42;
  // @skjs-expect-error The right-hand side of a 'for...in' statement must be an object or array type
  for (const _key in num) {
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
  let n: number;
  for (const key in obj) {
    // @skjs-expect-error Type is not assignable to the variable's type
    n = key; // string not assignable to number
  }
}

function testForOfWrongVariableType(): void {
  const arr = [1, 2, 3];
  let s: string;
  for (const value of arr) {
    // @skjs-expect-error Type is not assignable to the variable's type
    s = value; // number not assignable to string
  }
}

function testForInWithNull(): void {
  const nullObj = null;
  // @skjs-expect-error The right-hand side of a 'for...in' statement must be an object or array type
  for (const _key in nullObj) {
  }
}

function testForOfWithUndefined(): void {
  const undefinedArr = undefined;
  // @skjs-expect-error for-of loop requires an array, string, or iterable type
  for (const _value of undefinedArr) {
  }
}
