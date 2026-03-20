// When typeof wide & typeof narrow is intersected, wide <: narrow
// (wider params). Both cgNodes are preserved in the intersection
// result, so both fn:wide and fn:narrow reach fn:apply.

function wide(x: number | string): void {}
function narrow(x: number): void {}

function apply(f: typeof wide & typeof narrow): void {
  f(1);
}

// @skjs-callgraph-closure
// fn:wide: fn:apply
// fn:narrow: fn:apply
function test(): void {
  apply(wide);
}
