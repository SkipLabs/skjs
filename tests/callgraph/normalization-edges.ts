// Tests that subtypingEdges from type normalization substs (which are
// not flushed) are not needed for a correct dependency graph. Each
// section exercises a different normalization code path.

// --- Union type normalization ---
// TType::union on two function type aliases may internally compare
// them via TFun::isSub. The edges are on an ephemeral subst.
type Wide = (x: number | string) => void;
type Narrow = (x: number) => void;
type WideThenNarrow = Wide | Narrow;

function wideHandler(x: number | string): void {}

function applyWTN(f: WideThenNarrow): void {
  f(1);
}

// --- Intersection type normalization ---
// TType::inter on two function type aliases calls TFun::inter which
// calls TFun::isSub. The edges are on an ephemeral subst.
type InterWN = Wide & Narrow;

function applyInter(f: InterWN): void {
  f(1);
}

// --- Function type normalization ---
// Creating a TFun from a type annotation with function-typed params
// uses an ephemeral subst for normalization.
type Callback = (x: number) => void;

function myCallback(x: number): void {}

function applyCallback(f: Callback): void {
  f(1);
}

// --- Generic constraint check ---
// When instantiating a generic with a constraint, a cloned subst
// checks the argument against the constraint. The subtypingEdge on
// the clone is discarded.
function wrap<T extends Callback>(f: T): void {}

// @skjs-callgraph-closure
// fn:wideHandler: fn:applyWTN
// fn:wideHandler: fn:applyInter
// fn:myCallback: fn:applyCallback
function test(): void {
  applyWTN(wideHandler);
  applyInter(wideHandler);
  applyCallback(myCallback);
  wrap(myCallback);
}
