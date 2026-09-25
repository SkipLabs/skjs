// Arithmetic mixing a bigint and a number throws a TypeError: refused.
function mix(a: bigint, b: number): bigint {
  return a + b;
}
