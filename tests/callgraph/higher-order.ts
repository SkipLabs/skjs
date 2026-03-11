// @skjs-callgraph-full
// arrow-annot: fn:double
// fn:apply: arrow-annot
// fn:test: fn:apply

function apply(f: (x: number) => number, v: number): number {
  return f(v);
}
function double(x: number): number {
  return x * 2;
}
function test(): number {
  return apply(double, 5);
}
