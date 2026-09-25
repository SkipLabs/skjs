// A bigint divisor that may be zero throws a RangeError: refused, though
// TypeScript accepts it.
function share(total: bigint, parts: bigint): bigint {
  return total / parts;
}
