// Number literals beyond IEEE-754 double precision. Literals whose exact
// value is not representable in a double (radix literals above 2^53,
// exponents beyond the guard) are left in their spelled form. As TYPES they
// stay distinct (assignability compares names: sound, but stricter than tsc
// for two spellings of one double). Where a result depends on runtime values
// -- equality narrowing and truthiness -- they are compared by the double
// they denote, since two spellings can be one value (issue #781).

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

// 0xffffffffffffffff is 18446744073709552000 as a double, never -1. The
// always-false claim would be correct here, but spelled-form literals are
// conservatively treated as imprecise, so no warning is emitted.
function wraparoundAlwaysTrue(x: 0xffffffffffffffff, y: -1): boolean {
  return x === y;
}

// FIXME: tsc accepts: both literals are the double 9007199254740992 (2^53)
function hexVsDecimalSameDouble(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 9007199254740992 = 0x20000000000001;
}

// Both literals are the double 9007199254740992: the comparison is always
// true at runtime, so no non-overlap warning may be emitted for
// beyond-precision literal pairs.
function impreciseDecimalPair(
  x: 9007199254740993,
  y: 9007199254740992,
): boolean {
  return x === y;
}

// Both values are Infinity at runtime: same suppression.
function beyondRangePair(x: 1e309, y: 2e309): boolean {
  return x === y;
}

// #781: two spellings of one double. `x === y` is true at runtime (both are
// 2^53), so the branch is reachable and must not narrow to never.
function impreciseEqualityNarrowing(
  x: 9007199254740993 | "q",
  y: 9007199254740992 | "r",
): void {
  if (x === y) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: never = x;
  }
}

// Same with a radix spelling kept in source form (0x20000000000001 is 2^53+1,
// which rounds to the double 2^53).
function impreciseRadixEqualityNarrowing(
  x: 0x20000000000001 | "q",
  y: 9007199254740992 | "r",
): void {
  if (x === y) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: never = x;
  }
}

// #781: 1e-400 underflows to +0, a falsy value, so `x` has two falsy members
// and the condition is rejected. Its else branch keeps 1e-400 (it may be
// zero), so `x` is not `""` there -- tsc likewise reports `"" | 0`. Both were
// accepted when 1e-400 was read as truthy.
function underflowIsFalsy(x: 1e-400 | ""): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
    return;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "" = x;
}

// Spellings of one double as types. tsc accepts each: number literal types
// are keyed by their double. Pinned at current behavior: the spellings are
// distinct literal types, so each is rejected.
function sameDoubleDecimal(x: 9007199254740993): 9007199254740992 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function sameDoubleLong(x: 123456789012345678901): 123456789012345680000 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function fractionSameDouble(x: 0.300000000000000044): 0.30000000000000004 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 1e-400 underflows to 0; 1e309 and 2e309 both overflow to Infinity.
function underflowIsZero(x: 1e-400): 0 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function overflowSpellings(x: 2e309): 1e309 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// The printed literal type is its spelled form today.
function showBeyondPrecision(x: 9007199254740993, y: 1e-400, z: 2e309): void {
  __SKJS_show(x, "9007199254740993");
  __SKJS_show(y, "1e-400");
  __SKJS_show(z, "2e+309");
}
