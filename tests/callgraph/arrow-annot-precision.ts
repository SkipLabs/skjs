// Two unrelated higher-order functions (applyA and applyB) with the
// same callback type. Changes to fnA should only affect applyA, not
// applyB, and vice versa.
//
// All ArrowTypeAnnot nodes in the same file share a single CGNode
// (keyed only by fileName), so fnA and fnB are spuriously connected
// through the merged arrow-annot node. A fix would require both
// distinguishing ArrowTypeAnnot by position and ensuring the type
// checker preserves distinct CGNodes for structurally identical
// parameter types.

function fnA(x: number): void {}

function fnB(x: number): void {}

function applyA(f: (x: number) => void): void {
  f(1);
}

function applyB(f: (x: number) => void): void {
  f(2);
}

// @skjs-callgraph-closure
// fn:fnA: fn:applyA, fn:applyB
// fn:fnB: fn:applyA, fn:applyB
function test(): void {
  applyA(fnA);
  applyB(fnB);
}
