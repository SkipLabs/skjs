// @skjs-callgraph
// fn:test: fn:a, fn:b

function a(): number {
  return 1;
}
function b(): number {
  return 2;
}
function test(cond: boolean): number {
  return cond ? a() : b();
}
