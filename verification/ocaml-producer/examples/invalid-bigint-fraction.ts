// A number literal that is not an integer: `BigInt(1.5)` throws a RangeError.
function half(): bigint {
  return BigInt(1.5);
}
