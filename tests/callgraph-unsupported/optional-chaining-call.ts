// FIXME: missing callgraph edge for optional chaining calls
interface Obj {
  method(): number;
}
function test(o: Obj | undefined): number | undefined {
  // @skjs-expect-error Invalid call
  return o?.method();
}
