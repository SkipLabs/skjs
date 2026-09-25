// Booleans compared relationally convert to numbers first: outside the
// operator rule, though TypeScript accepts it.
function order(a: boolean, b: boolean): boolean {
  return a < b;
}
