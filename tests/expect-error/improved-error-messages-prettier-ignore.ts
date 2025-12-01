// Test improved error messages for parsing errors

// Test: Better error when unexpected token in type position
function testUnexpectedTokenInType(): void {
  // @ts-expect-error Expected token ' or " or ` or < or [ or ( or { or - or a number or a bigint or a variable name
  const x: * = 5;
