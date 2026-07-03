// Number literals beyond IEEE-754 double precision. SKJS normalizes radix
// literals and exponents with exact 64-bit integer arithmetic, which wraps
// silently at 2^63 instead of rounding to a double like JavaScript.

// FIXME: 0xffffffffffffffff is 18446744073709552000, never -1 (Int64 wraparound)
function hexWraparound(): void {
  const a: -1 = 0xffffffffffffffff;
}

// FIXME: exponent digits wrap mod 2^64 (2^64 + 3 -> 3), equating this literal with 1000
function exponentWraparound(): void {
  const a: 1000 = 1e18446744073709551619;
}

// FIXME: the runtime key is "18446744073709552000"; SKJS wraps the field name to "-1"
function fieldWraparound(x: { 0xffffffffffffffff: string }): { "-1": string } {
  return x;
}

// FIXME: 0xffffffffffffffff is 18446744073709552000 as a double, never -1,
// so this comparison is always false
function wraparoundAlwaysTrue(x: 0xffffffffffffffff, y: -1): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

// FIXME: tsc accepts: both literals are the double 9007199254740992 (2^53)
function hexVsDecimalSameDouble(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 9007199254740992 = 0x20000000000001;
}

// FIXME: both literals are the double 9007199254740992, so x === y is always true
function impreciseDecimalPair(
  x: 9007199254740993,
  y: 9007199254740992,
): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

// FIXME: both values are Infinity at runtime, so x === y is always true
function beyondRangePair(x: 1e309, y: 2e309): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}
