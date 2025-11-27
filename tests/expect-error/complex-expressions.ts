// Test complex expressions that combine multiple operators

function testPostfixWithMultipleOps(): void {
  let x: number = 5;
  let y: number = 3;
  let z: number = 2;

  // Postfix with multiple binary operators
  const a = x++ + y * z; // Should parse as: (x++) + (y * z)
  const b = x++ - y++ + z++; // Should parse as: ((x++) - (y++)) + (z++)
  const c = (x++ * y++) / z++; // Should parse as: ((x++) * (y++)) / (z++)
}

function testTernaryWithBinaryOps(): void {
  const x: number = 5;
  let y: number = 3;

  // Ternary with binary operators in branches
  const a = x > 0 ? x + y : x - y; // Should parse correctly
  const b = x > 0 ? y++ : y--; // Ternary with postfix in branches
}

function testComplexPrecedence(): void {
  let x: number = 5;
  let y: number = 3;
  let z: number = 2;

  // Multiple operators with different precedence levels
  const a = x + y * z; // Should parse as: x + (y * z)
  const b = x * y + z; // Should parse as: (x * y) + z
  const c = x + y - z * 2; // Should parse as: (x + y) - (z * 2)
}

function testFunctionCallWithComplexArgs(): void {
  let add = (a: number, b: number): number => a + b;
  let x: number = 5;
  let y: number = 3;

  // Function call with postfix in arguments
  const a = add(x++, y++); // Should parse as: add((x++), (y++))

  // Function call result used in expression
  const b = add(x, y) + x++; // Should parse as: (add(x, y)) + (x++)
}

function testMemberAccessWithComplexOps(): void {
  const obj = { count: 5, value: 10 };

  // Member access with postfix and binary operators
  const a = obj.count++ + obj.value; // Should parse as: (obj.count++) + (obj.value)
  const b = obj.count++ * 2 + obj.value--; // Should parse as: ((obj.count++) * 2) + (obj.value--)
}
