// @skjs-callgraph
// fn:test: method:Obj.method
interface Obj {
  method(): number;
}
function test(o: Obj | undefined): number | undefined {
  return o?.method();
}
