// Tests that number literals are normalized to canonical JS form.
// In JavaScript, 1.0 === 1, 0x10 === 16, 1e3 === 1000, 1_000 === 1000.
// SKJS should normalize all these to their canonical String(Number(x)) form.

// --- Type literal equivalence ---

function testDecimalOne(): void {
  const a: 1 = 1.0;
}

function testDecimalOneReverse(): void {
  const a: 1.0 = 1;
}

function testHexLiteral(): void {
  const a: 16 = 0x10;
}

function testBinaryLiteral(): void {
  const a: 2 = 0b10;
}

function testScientific(): void {
  const a: 1000 = 1e3;
}

function testUnderscore(): void {
  const a: 1000 = 1_000;
}

function testNegativeDecimal(): void {
  const a: -1 = -1.0;
}

// --- Field name equivalence ---

function testDecimalFieldName(x: { 1.0: string }): { 1: string } {
  return x;
}

function testHexFieldName(x: { 0x10: string }): { 16: string } {
  return x;
}

function testUnderscoreFieldName(x: { 1_000: string }): { 1000: string } {
  return x;
}

function testScientificFieldName(x: { 1e3: string }): { 1000: string } {
  return x;
}

// --- Octal and binary field names ---

function testOctalValue(): void {
  const a: 15 = 0o17;
}

function testOctalFieldName(x: { 0o17: string }): { 15: string } {
  return x;
}

function testBinaryFieldName(x: { 0b10: string }): { 2: string } {
  return x;
}

// --- Negative control: normalization must not conflate distinct values ---

function testMismatchStillErrors(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1001 = 1e3;
}
