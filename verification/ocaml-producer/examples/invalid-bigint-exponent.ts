// A negative bigint exponent throws a RangeError: refused, though TypeScript
// accepts it.
function inverse(x: bigint): bigint {
  return x ** -1n;
}
