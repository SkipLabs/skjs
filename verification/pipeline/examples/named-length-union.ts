// `length` of a union of an array and a record naming it: the array keeps
// its length in its store, the record at a field; refused by name.
export function size(x: number[] | { name: string; length: number }): number {
  return x.length;
}
