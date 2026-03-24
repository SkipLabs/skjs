// @skjs-callgraph
//
// Missing edge (uncomment when implicit iterator calls are tracked):
//   fn:test: <Symbol.iterator>, <next>
// fn:test should depend on the user-defined Symbol.iterator and next
// implementations, but spread implicitly calls these with no call graph edge.
interface MyIterable {
  [Symbol.iterator](): { next(): { readonly value: number; done: boolean } };
}
function test(iter: MyIterable): number[] {
  return [...iter];
}
