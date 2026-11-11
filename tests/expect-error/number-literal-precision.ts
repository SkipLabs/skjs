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
// 2^53), so the branch is reachable and must not narrow to never. Pinned at
// current behavior: the branch narrows to never and the assignment is
// silently accepted.
function impreciseEqualityNarrowing(
  x: 9007199254740993 | "q",
  y: 9007199254740992 | "r",
): void {
  if (x === y) {
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
    const z: never = x;
  }
}

// #781: 1e-400 underflows to +0, a falsy value, so `x` has two falsy members.
// Pinned at current behavior: 1e-400 is classified truthy, so the condition is
// accepted and the else branch narrows to "" although x can be 0 there.
function underflowIsFalsy(x: 1e-400 | ""): void {
  if (x) {
    return;
  }
  const z: "" = x;
}
