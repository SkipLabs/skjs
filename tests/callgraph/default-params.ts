// @skjs-callgraph
// fn:bar: fn:foo
// fn:foo: fn:getDefault

function getDefault(): number {
  return 0;
}
function foo(x: number = getDefault()): number {
  return x;
}
function bar(): number {
  return foo();
}
