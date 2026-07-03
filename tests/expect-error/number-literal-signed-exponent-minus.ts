// ES exponent parts may carry a sign: 1e-3 is the literal 0.001.

function signedExponentMinus(): void {
  const a: 0.001 = 1e-3;
}

function signedExponentType(): void {
  const a: 1e-7 = 0.0000001;
}

// The sign is only part of the literal right after the exponent marker:
// these stay arithmetic.
function subtractionAfterDigit(): number {
  const a: number = 1e2 - 3;
  return a;
}

function additionAfterHexDigit(): number {
  const a: number = 0x1e + 2;
  return a;
}
