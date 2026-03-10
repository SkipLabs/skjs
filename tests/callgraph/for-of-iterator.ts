// @skjs-callgraph
//
// Missing edge (uncomment when implicit iterator calls are tracked):
//   fn:test: <Symbol.iterator>, <next>
// fn:test should depend on the user-defined Symbol.iterator and next
// implementations, but for...of implicitly calls these with no call graph edge.
// For built-in iterables (arrays, strings), this is not a concern since the
// iterator implementation is not user code.
interface MyIterable {
  [Symbol.iterator](): { next(): { readonly value: number; done: boolean } };
}
function test(iter: MyIterable): number {
  let sum = 0;
  for (const n of iter) {
    sum += n;
  }
  return sum;
}
