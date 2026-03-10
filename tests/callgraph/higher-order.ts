// @skjs-callgraph-full
// fn:apply: arrow-annot
// fn:test: fn:apply
//
// Missing edge: fn:apply should also depend on fn:double (and any other
// function passed as f), since f(v) can call double at runtime. Currently
// only arrow-annot is recorded because f's type comes from the parameter
// annotation, not the concrete function passed at the call site.

function apply(f: (x: number) => number, v: number): number {
  return f(v);
}
function double(x: number): number {
  return x * 2;
}
function test(): number {
  return apply(double, 5);
}
