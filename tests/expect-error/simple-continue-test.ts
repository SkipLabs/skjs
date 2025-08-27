// Simple test to check if continue works in basic for loops

function testContinue(): void {
  for (let i = 0; i < 5; i++) {
    if (i === 2) {
      continue; // This should skip iteration when i=2
    }
    console.log(i); // Should print 0, 1, 3, 4
  }
}
