// @skjs-callgraph
//
// Missing edge (uncomment when implicit await calls are tracked):
//   fn:test: <Promise.then>
// fn:test should depend on the promise's .then() implementation,
// but await implicitly calls .then() with no call graph edge.
// In practice, promise machinery is built-in rather than user-defined.
async function test(p: Promise<number>): Promise<number> {
  return await p;
}
