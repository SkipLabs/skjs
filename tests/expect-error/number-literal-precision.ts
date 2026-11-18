// Number literals beyond IEEE-754 double precision (16+ significant digits,
// radix literals above 2^53, exponents outside the double range). Like tsc,
// SKJS keys a number literal type by the double it denotes (issue #781): a
// beyond-precision literal is named by that double's ECMAScript String()
// form, so two spellings of one double are one literal type
// (`9007199254740993` is `9007199254740992`, `1e-400` is `0`, `1e309` is
// `Infinity`). A name the runtime cannot parse keeps its spelled form;
// equality narrowing, truthiness and the always-true/false comparison
// warnings then assume it may be any value.

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

// Number literal names are the String() form of their double, so distinct
// names are distinct values and comparing them is always false, as tsc
// reports (TS2367): 0xffffffffffffffff is 18446744073709552000, never -1.
function wraparoundAlwaysTrue(x: 0xffffffffffffffff, y: -1): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function distinctBeyondPrecision(
  x: 9007199254740993,
  y: 9007199254740994,
): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function distinctSixteenDigits(
  x: 0.1234567890123456,
  y: 0.1234567890123457,
): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function distinctRangeEdges(x: 1e308, y: 1e-308): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

// Both literals are the double 9007199254740992 (2^53): one literal type.
function hexVsDecimalSameDouble(): void {
  const a: 9007199254740992 = 0x20000000000001;
}

// Both literals are the double 9007199254740992, one literal type, so the
// operands always hold the same single value.
function impreciseDecimalPair(
  x: 9007199254740993,
  y: 9007199254740992,
): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

// Both values are Infinity at runtime: one literal type, `Infinity`.
function beyondRangePair(x: 1e309, y: 2e309): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
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

// #781: 1e-400 underflows to +0, so its literal type is `0`: `x` has two
// falsy members and the condition is rejected, and the else branch keeps `0`
// -- tsc likewise reports `"" | 0`. Both were accepted when 1e-400 was read
// as a truthy literal.
function underflowIsFalsy(x: 1e-400 | ""): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
    return;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "" = x;
}

// Spellings of one double are one literal type, as in tsc.
function sameDoubleDecimal(x: 9007199254740993): 9007199254740992 {
  return x;
}

function sameDoubleLong(x: 123456789012345678901): 123456789012345680000 {
  return x;
}

function fractionSameDouble(x: 0.300000000000000044): 0.30000000000000004 {
  return x;
}

// 1e-400 underflows to 0.
function underflowIsZero(x: 1e-400): 0 {
  return x;
}

// 1e309 and 2e309 both overflow to Infinity: one literal type.
function overflowSpellings(x: 2e309): 1e309 {
  return x;
}

// A literal type prints as the String() form of its double.
function showBeyondPrecision(x: 9007199254740993, y: 1e-400, z: 2e309): void {
  __SKJS_show(x, "9007199254740992");
  __SKJS_show(y, "0");
  __SKJS_show(z, "Infinity");
}

// Infinity literals are named Infinity / -Infinity, as in tsc: every
// spelling of an overflowing value is one literal type, and it is the
// numeric property name "Infinity".
function infinitySpellings(x: 2e309): 1e309 {
  return x;
}

function infinityShow(x: 1e309, y: -1e309): void {
  __SKJS_show(x, "Infinity");
  __SKJS_show(y, "-Infinity");
}

// +Infinity is not -Infinity (rejected by tsc too).
function infinitySign(x: 1e309): -1e309 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function infinityKey(o: { 1e309: number }): { Infinity: number } {
  return o;
}

// Infinity is truthy, so `x` has a single falsy member.
function infinityTruthy(x: 1e309 | ""): void {
  if (x) {
    return;
  }
  const z: "" = x;
}

// keyof sees the Infinity key both as the string "Infinity" and as the
// number literal Infinity (the literal 1e309), as for any numeric key.
function infinityKeyof(o: { 1e309: 1; 5: 2 }): void {
  const k: keyof typeof o = 1e309;
  const s: keyof typeof o = "Infinity";
}
