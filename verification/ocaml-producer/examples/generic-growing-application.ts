// A generic method whose result applies its own interface at arguments that
// keep growing: Pair<number>'s push returns Pair<[number, U]>, whose push
// returns Pair<[[number, U], U']>, ... Lowering stops where the arguments
// pass the budget, leaving push opaque there, and the type is a finite graph.
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
export function first(p: Pair<number>): number {
  return p.first();
}
