// `BigInt(1.5)` throws a RangeError, so `BigInt` of an arbitrary number is
// refused, though TypeScript's declaration admits every number.
function toBig(x: number): bigint {
  return BigInt(x);
}
