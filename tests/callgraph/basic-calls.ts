// @skjs-callgraph
// fn:bar: fn:foo
// fn:baz: fn:bar

function foo(): number {
  return 1;
}
function bar(): number {
  return foo();
}
function baz(): number {
  return bar();
}
