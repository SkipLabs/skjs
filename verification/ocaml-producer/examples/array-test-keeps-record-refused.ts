// `Array.isArray` keeps a record arm on both outcomes: a value of the
// record's type may be an array carrying its keys. A member only the array
// states is then refused on the union.
interface Foo {
  a: string;
}
export function length(x: number[] | Foo): number {
  if (Array.isArray(x)) {
    return x.length;
  }
  return 0;
}
