// Test to reproduce string indexing issue

function testStringIndexing(): void {
  const str = "hello";
  
  // This should work - accessing string by index
  const char = str[0]; // Should be type string | undefined
  
  console.log(char); // Should print 'h'
}

function testStringIndexingTypes(): void {
  const message = "world";
  
  // Test various index access patterns
  const first = message[0];     // Should be string | undefined
  const middle = message[2];    // Should be string | undefined  
  const last = message[4];      // Should be string | undefined
  const outOfBounds = message[10]; // Should be string | undefined
  
  // Test with variable index
  const index = 1;
  const charAtIndex = message[index]; // Should be string | undefined
}

function testStringIndexingWithNumbers(): void {
  const text = "test";
  
  // Test with different number types
  const a = text[0];
  const b = text[1.0];  // Should still work
  const c = text[2];
}