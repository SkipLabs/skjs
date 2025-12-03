// Test assignment operator right-associativity
// Assignment is right-associative: a = b = c should parse as a = (b = c)

function testChainedAssignment(): void {
  let a: number = 0;

  // FIXME!
  // @skjs-expect-error Invalid lvalue
  a = a = a;
}
