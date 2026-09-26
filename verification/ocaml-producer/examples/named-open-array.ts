// `Array.isArray` on an open record finds it owns an array's store, not that
// it is an array of `Array.prototype`: refused by name where it is used as
// an array.
type Foo = { a: string; b: number };

export function elements(x: number[] | Foo): readonly unknown[] {
  if (Array.isArray(x)) return x;
  return [];
}
