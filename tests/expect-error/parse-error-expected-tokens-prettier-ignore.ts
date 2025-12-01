// Test that parse errors show expected tokens

// Test: Unexpected token in type position shows expected tokens
function testUnexpectedTokenInType(): void {
  // @ts-expect-error Expected token ' or " or ` or < or [ or ( or { or - or a number or a bigint or a variable name
  const x: * = 5;
