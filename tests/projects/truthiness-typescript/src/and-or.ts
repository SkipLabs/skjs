// In "typescript" mode `&&`/`||` largely match tsc: a number left operand is
// fine (returning the value type), and an always-truthy function reference is
// rejected (TS2774), in `&&`/`||` just like in a plain condition. The one known
// gap is the precision of the value type — see `andValueWiderThanTsc` below.

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

// The over-approximated result type is accepted: `s && b` is `string | number`
// here (a supertype of tsc's `"" | number`), so the wide annotation type-checks.
function andValueWide(s: string, b: number): string | number {
  return s && b;
}

// FIXME: known SKJS/tsc divergence. The falsy operand of `&&`/`||` is
// over-approximated to the whole type (`truthinessResidue` in src/TType.sk), so
// `s && b` is typed `string | number` here, whereas tsc narrows the falsy side
// and types it `"" | number`. The wider type is sound — it never accepts
// unsound code — but rejects this assignment that tsc accepts.
function andValueWiderThanTsc(s: string, b: number): "" | number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s && b;
}

// FIXME: same divergence for bigint: the only falsy bigint is `0n`, so tsc
// types `bi && s` as `0n | string`, while SKJS keeps the whole `bigint` on the
// falsy side.
function andValueBigint(bi: bigint, s: string): 0n | string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return bi && s;
}

// FIXME: same divergence for number: tsc types `n && s` as `0 | string`.
function andValueNumberFalsy(n: number, s: string): 0 | string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n && s;
}
