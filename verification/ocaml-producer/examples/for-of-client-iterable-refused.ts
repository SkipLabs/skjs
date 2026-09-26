// An `Iterable<number>` may be any object with a `[Symbol.iterator]`: its own
// iterator runs, and a loop left early, by `return` here, calls its `return`,
// which the loop does not state.
export function first(values: Iterable<number>): number {
  for (const v of values) return v;
  return 0;
}
