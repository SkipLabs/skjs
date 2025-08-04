// Comprehensive test for string indexing functionality

function testBasicStringIndexing(): void {
  const str = "hello";
  
  // Basic numeric indexing should work
  const char0 = str[0];  // Should be string | undefined
  const char1 = str[1];  // Should be string | undefined  
  const char4 = str[4];  // Should be string | undefined
  
  console.log(char0, char1, char4);
}

function testStringIndexingWithVariables(): void {
  const message = "world";
  const index = 2;
  
  // Variable index should work
  const char = message[index]; // Should be string | undefined
  console.log(char);
}

function testStringIndexingOutOfBounds(): void {
  const text = "hi";
  
  // Out of bounds access should still be string | undefined
  const char = text[10]; // Should be string | undefined
  console.log(char);
}

function testStringIndexingWithExpressions(): void {
  const str = "test";
  
  // Expression as index should work
  const char1 = str[1 + 1]; // Should be string | undefined
  const char2 = str[0 * 5]; // Should be string | undefined
  
  console.log(char1, char2);
}

// Test that static string indexing still works for properties
function testStringPropertyAccess(): void {
  const str = "example";
  
  // This should work for accessing string properties (if they exist)
  // Note: We're testing the parsing/typing, not runtime behavior
}

// Test type compatibility - string | undefined should work where expected
function testStringIndexingTypeCompatibility(): void {
  const str = "hello";
  const maybeChar = str[0]; // string | undefined
  
  // Should be able to assign to string | undefined
  const result: string | undefined = maybeChar;
  
  // Should be able to use in conditionals
  if (maybeChar !== undefined) {
    console.log(maybeChar); // Now it's narrowed to string
  }
}

function testStringIndexingInConditions(): void {
  const text = "conditional";
  
  // Should work in boolean contexts
  if (text[0]) {
    console.log("First character exists");
  }
  
  if (text[100]) {
    console.log("This won't run");
  }
}

function testStringIndexingWithDifferentNumberTypes(): void {
  const str = "numbers";
  
  // Different ways to specify numbers
  const a = str[0];       // integer literal
  const b = str[1.0];     // float literal (should work as 1)
  const c = str[2];       // another integer
  
  console.log(a, b, c);
}

// Test edge cases
function testStringIndexingEdgeCases(): void {
  const empty = "";
  const single = "a";
  
  // Empty string
  const char1 = empty[0]; // Should be string | undefined
  
  // Single character string
  const char2 = single[0]; // Should be string | undefined
  const char3 = single[1]; // Should be string | undefined (out of bounds)
  
  console.log(char1, char2, char3);
}