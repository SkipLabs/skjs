// Number literals beyond IEEE-754 double precision. Literals whose exact
// value is not representable in a double (radix literals above 2^53,
// exponents beyond the guard) are left in their spelled form and compare
// textually: sound, but two spellings of the same double stay distinct
// literal types (stricter than tsc for such pairs).

function hexWraparound(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: -1 = 0xffffffffffffffff;
}

function exponentWraparound(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1000 = 1e18446744073709551619;
}

function fieldWraparound(x: { 0xffffffffffffffff: string }): { "-1": string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 0xffffffffffffffff is 18446744073709552000 as a double, never -1: the
// spelled forms do not overlap, and neither do the runtime values.
function wraparoundAlwaysTrue(x: 0xffffffffffffffff, y: -1): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
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
