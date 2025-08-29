// Test to verify that string indexing returns string | undefined

function testStringIndexingType(): void {
  const str = "hello";
  const char = str[0];

  // This should work - assigning to string | undefined
  const result: string | undefined = char;

  // This should also work - checking for undefined
  if (char === undefined) {
    console.log("Character is undefined");
  }

  // This should work - checking for string
  if (typeof char === "string") {
    console.log("Character is a string");
  }
}

function testStringIndexingInUnion(): void {
  const text = "test";

  // Should be able to use in union types
  const value: string | undefined | number = text[0];
  console.log(value);
}

// Test to ensure we can handle the undefined case
function testUndefinedHandlingInline(): void {
  const str = "world";
  const char = str[0];

  // TODO: Should work with undefined checks
  // @ts-expect-error Type cannot be accessed
  const length = char !== undefined ? char.length : 0;
  console.log(length);
}

// Test to ensure we can handle the undefined case
function testUndefinedHandling(): number {
  const str = "world";
  const char = str[0];

  // Should work with undefined checks
  if (char !== undefined) {
    return char.length;
  }
  return 0;
}
