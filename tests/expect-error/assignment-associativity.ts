// Test assignment operator right-associativity
// Assignment is right-associative: a = b = c should parse as a = (b = c)

function testChainedAssignment(): void {
  let a: number = 0;

  a = a = a;
}
