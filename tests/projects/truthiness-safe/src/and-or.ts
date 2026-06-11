// `&&` / `||` are value-returning (JavaScript semantics) in every mode: the
// return-type annotations assert the result type. The left operand follows the
// "safe" rule, so a number left operand is rejected (the `count || default`
// footgun) even though tsc accepts it.

// `a && b` is (falsy part of a) | b.
function andUndef(o: { a: number } | undefined, n: number): undefined | number {
  return o && n;
}

// `a || b` is (truthy part of a) | b.
function orObj(
  o: { a: number } | undefined,
  d: { b: number },
): { a: number } | { b: number } {
  return o || d;
}

// The left operand is narrowed for the right operand, so `o.a` is valid here.
function andNarrows(o: { a: number } | undefined): undefined | number {
  return o && o.a;
}

// boolean operands keep a boolean result.
function boolAnd(x: boolean, y: boolean): boolean {
  return x && y;
}

// Rejected: number is not single-falsy, so it cannot be the truthiness-tested
// left operand (tsc accepts this, returning number).
function rejectNumberOr(count: number): number {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  return count || 10;
}
