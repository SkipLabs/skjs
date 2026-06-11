// In "typescript" mode `&&`/`||` largely match tsc: a number left operand is
// fine (returning the value type), and an always-truthy function reference is
// rejected (TS2774), in `&&`/`||` just like in a plain condition. The one known
// gap is a `number` falsy operand — see `andValueNumberFalsy` below.

// Accepted: number left operand (tsc returns number here too).
function acceptNumberOr(count: number): number {
  return count || 10;
}

// Rejected: the left operand is an always-truthy function reference. Its falsy
// part is empty, so `fn && n` has type `number`.
function rejectFunctionAnd(fn: () => void, n: number): number {
  // @ts-expect-error This condition will always be true since this value is always defined
  return fn && n;
}

// The precise result type still satisfies a wide annotation: `s && b` is
// `"" | number`, a subtype of `string | number`.
function andValueWide(s: string, b: number): string | number {
  return s && b;
}

// The falsy operand of `&&`/`||` is narrowed to its falsy values where that is
// precise: the only falsy string is `""`, so `s && b` is `"" | number`,
// matching tsc.
function andValuePrecise(s: string, b: number): "" | number {
  return s && b;
}

// Same for bigint: the only falsy bigint is `0n`, so `bi && s` is
// `0n | string`, matching tsc.
function andValueBigint(bi: bigint, s: string): 0n | string {
  return bi && s;
}

// FIXME: known SKJS/tsc divergence. tsc types `n && s` as `0 | string`, but
// `number`'s falsy values are `0`, `-0` and `NaN`, and `NaN` has no literal
// type — narrowing to `0` would be unsound (`NaN && s` evaluates to `NaN`), so
// SKJS keeps the whole `number` on the falsy side and rejects this assignment
// that tsc accepts.
function andValueNumberFalsy(n: number, s: string): 0 | string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n && s;
}
