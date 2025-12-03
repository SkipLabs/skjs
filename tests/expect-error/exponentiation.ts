// Test exponentiation operator

const testExponentiationNumbers: number = 2 ** 3;

const testExponentiationBigInt: bigint = 2n ** 3n;

function testExponentiationAssignment(): void {
  let x: number = 2;
  x **= 3;
}

// @ts-expect-error Arithmetic operations require both operands to be the same numeric type
const testExponentiationTypeMismatch: bigint = 2 ** 3n;

// @ts-expect-error Invalid operation
const testExponentiationInvalidTypes: number = 2 ** "3";
