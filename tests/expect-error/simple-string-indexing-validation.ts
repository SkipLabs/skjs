// Simple validation test for string indexing

function testStringIndexing(): void {
  const str = "hello";

  // Test basic indexing
  const char0 = str[0]; // Should be string | undefined
  const char1 = str[1]; // Should be string | undefined
  const char4 = str[4]; // Should be string | undefined
  const outOfBounds = str[10]; // Should be string | undefined

  console.log(char0);
}

function testVariableIndex(): void {
  const message = "world";
  const index = 2;

  // Variable index
  const char = message[index]; // Should be string | undefined
  console.log(char);
}

function testExpressionIndex(): void {
  const text = "test";

  // Expression as index
  const char1 = text[1 + 1]; // Should be string | undefined
  const char2 = text[0 * 5]; // Should be string | undefined

  console.log(char1);
}

// Test type assignment
function testTypeAssignment(): void {
  const str = "example";
  const maybeChar = str[0]; // string | undefined

  // Should be assignable to string | undefined
  const result: string | undefined = maybeChar;
  console.log(result);
}

// Test conditional check
function testConditionalCheck(): void {
  const text = "conditional";
  const char = text[0];

  // Test with explicit undefined check
  if (char !== undefined) {
    console.log(char); // Should be narrowed to string here
  }
}

function testFloatIndex(): void {
  const str = "float";

  // Float indices (should work as integers)
  const a = str[1.0]; // Should work as str[1]
  const b = str[2.0]; // Should work as str[2]

  console.log(a);
}

function testEmptyString(): void {
  const empty = "";

  // Empty string indexing
  const char = empty[0]; // Should be string | undefined
  console.log(char);
}
