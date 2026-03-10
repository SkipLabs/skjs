// FIXME: missing callgraph edge for optional chaining calls
// skjs-callgraph
// fn:test: method:Obj.method
interface Obj {
  method(): number;
}
function test(o: Obj | undefined): number | undefined {
  // @skjs-expect-error Invalid call
  return o?.method();
}
