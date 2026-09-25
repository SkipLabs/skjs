// A radix that may be any number may be one `toString` throws on, though
// TypeScript's declaration admits every number.
function anyRadix(n: number, radix: number): string {
  return n.toString(radix);
}
