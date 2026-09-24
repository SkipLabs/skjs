// The standard library's Iterable reaches Iterator, whose `next` takes a
// destructured rest parameter, `...[value]: [] | [TNext]`, outside the
// declaration fragment.
export function same(x: Iterable<number>): Iterable<number> {
  return x;
}
