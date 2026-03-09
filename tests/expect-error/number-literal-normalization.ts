// Tests that number literals are normalized to canonical JS form.
// In JavaScript, 1.0 === 1, 0x10 === 16, 1e3 === 1000, 1_000 === 1000.
// SKJS should normalize all these to their canonical String(Number(x)) form.

// --- Type literal equivalence ---

// FIXME: 1.0 and 1 are the same JS number
function testDecimalOne(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1 = 1.0;
}

// FIXME: 1.0 and 1 are the same JS number
function testDecimalOneReverse(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1.0 = 1;
}

// FIXME: 0x10 is 16
function testHexLiteral(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 16 = 0x10;
}

// FIXME: 0b10 is 2
function testBinaryLiteral(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 2 = 0b10;
}

// FIXME: 1e3 is 1000
function testScientific(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1000 = 1e3;
}

// FIXME: 1_000 is 1000
function testUnderscore(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1000 = 1_000;
}

// FIXME: -1.0 is -1
function testNegativeDecimal(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: -1 = -1.0;
}

// --- Field name equivalence ---

// FIXME: field 1.0 is field "1"
function testDecimalFieldName(x: { 1.0: string }): { 1: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// FIXME: field 0x10 is field "16"
function testHexFieldName(x: { 0x10: string }): { 16: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// FIXME: field 1_000 is field "1000"
function testUnderscoreFieldName(x: { 1_000: string }): {
  1000: string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// FIXME: field 1e3 is field "1000"
function testScientificFieldName(x: { 1e3: string }): {
  1000: string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}
