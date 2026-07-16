// Test that parse errors show expected tokens

// Test: Unexpected token in type position shows expected tokens
function testUnexpectedTokenInType(): void {
  // @skjs-expect-error ''' or '"' or 'a template literal' or '<' or '[' or '(' or '{' or '-' or 'a number' or 'a bigint' or 'a variable name' expected
  const x: * = 5;
