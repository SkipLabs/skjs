// `Array.isArray` on `unknown` finds that the value owns an array's store,
// not that it is an array of `Array.prototype`: the array invariant is a fact
// of every record and dictionary type, and `unknown` is also the type a
// handler binds a thrown value at, of which the model states nothing.
export function elements(x: unknown): readonly unknown[] {
  if (Array.isArray(x)) return x;
  return [];
}
