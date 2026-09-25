// `toString` throws a RangeError for a radix outside 2 to 36.
function badRadix(n: number): string {
  return n.toString(1);
}
