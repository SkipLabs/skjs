// Calling push substitutes string for U in the recursive result family. A
// faithful implementation must relate the complete equations of Pair<[number,
// U]> and Pair<[number, string]>, not compare differently truncated graphs.
// The current lowering refuses the whole contract at its expansion limit.
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
export function one(p: Pair<number>): Pair<[number, string]> {
  return p.push("a");
}
