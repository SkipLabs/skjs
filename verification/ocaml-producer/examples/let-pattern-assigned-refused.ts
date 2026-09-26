// A `let` pattern whose binding a later statement assigns: each binding
// would be a cell with a storage contract of its own, which a pattern does
// not lower to.
export function assigned(pair: readonly [number, string]): number {
  let [n] = pair;
  n = n + 1;
  return n;
}
