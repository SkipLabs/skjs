// Calling push: its instance relates the scheme's result, Pair<[number, U]>,
// to Pair<[number, string]>. Both unfold without end at growing arguments,
// and each stops where its own arguments exhaust the colours or the budget,
// at different depths, so the two graphs are not renamings of each other.
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
export function one(p: Pair<number>): Pair<[number, string]> {
  return p.push("a");
}
