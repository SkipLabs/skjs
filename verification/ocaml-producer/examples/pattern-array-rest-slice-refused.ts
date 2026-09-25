// The rest of an array of unknown length is a slice of a length known only at
// run time: no fixed list of reads, and the calculus has no slice.
export function restFromArray(arr: number[]): number[] {
  const [first, ...rest] = arr;
  return rest;
}
