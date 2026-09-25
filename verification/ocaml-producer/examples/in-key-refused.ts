// A key of type `string` may be any key, `toString` or an array index
// included, which the model's own-key test does not answer as JavaScript
// does: only a union of string literals is read.
export function any(s: string, x: { f: number }): boolean {
  return s in x;
}
