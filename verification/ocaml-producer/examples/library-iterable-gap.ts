// The standard library's Iterable reaches Iterator, whose `return?` and
// `throw?` are optional methods: a field that may be absent needs presence
// semantics.
export function same(x: Iterable<number>): Iterable<number> {
  return x;
}
