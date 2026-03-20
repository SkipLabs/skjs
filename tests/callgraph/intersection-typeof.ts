// FIXME: TFun::inter drops cgNodes from the non-subtype operand.
// When typeof wide & typeof narrow is intersected, wide <: narrow
// (wider params), so the result is wide's TFun — narrow's cgNode
// is lost. Changes to narrow would not propagate to apply.
//
// The closure assertion below documents the INCORRECT behavior:
// fn:narrow should reach fn:apply but currently does not.

function wide(x: number | string): void {}
function narrow(x: number): void {}

function apply(f: typeof wide & typeof narrow): void {
  f(1);
}

// @skjs-callgraph-closure
// fn:wide: fn:apply
//
// FIXME: fn:narrow should also reach fn:apply but doesn't
// (cgNode lost in TFun::inter)
function test(): void {
  apply(wide);
}
