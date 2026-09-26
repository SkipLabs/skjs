// A spread of an `Iterable<number>` runs its own iterator, which may be any
// code: the spread does not state it.
function sum(...xs: number[]): number {
  return xs.length;
}

export function spread(values: Iterable<number>): number {
  return sum(...values);
}
