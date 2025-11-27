// Test postfix operators work correctly with binary operators

function testPostfixPlusBinary(): void {
  let x: number = 5;
  let y: number = 3;

  // Postfix ++ followed by binary operator
  const a = x++ + y; // Should parse as: (x++) + y = 5 + 3 = 8, then x becomes 6

  // Postfix -- followed by binary operator
  const b = x-- - y; // Should parse as: (x--) - y

  // Multiple postfix and binary
  const c = x++ * y++ + 1; // Should parse as: ((x++) * (y++)) + 1

  // Postfix with comparison
  const d = x++ < y; // Should parse as: (x++) < y

  // Postfix with logical operators
  const e = x++ > 0 && y-- > 0; // Should parse as: ((x++) > 0) && ((y--) > 0)
}

function testPostfixWithMemberAccess(): void {
  const obj = { count: 5 };

  // Postfix on member access followed by binary op
  const a = obj.count++ + 10; // Should parse as: (obj.count++) + 10
}

function testPostfixWithFunctionCall(): void {
  let getNumber = (): number => 5;
  let x: number = 0;

  // Postfix followed by function call result
  const a = x++ + getNumber(); // Should parse as: (x++) + getNumber()
}
