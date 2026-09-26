// A key a `for...in` loop yields is read at the dictionary's index, which may
// miss: that the object owns the key relates two values.
export function sum(v: { [k: string]: number }): number {
  let total = 0;
  for (const k in v) {
    total = total + v[k]!;
  }
  return total;
}
