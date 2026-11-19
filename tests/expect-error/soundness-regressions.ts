// Witnessed soundness holes, each already rejected on main, pinned at the
// exact program from its issue so a regression reopening it fails here.

// #1039: enum constant folding. 1e-400 underflows to 0, so the member's
// runtime value is "x0"; its literal type must not be "x1e-400". Fixed by the
// beyond-precision literal canonicalization (#1067): the member is "x0".
enum UnderflowConcat {
  // @skjs-expect-warning Number literal '1e-400' underflows to 0
  A = "x" + 1e-400,
}

function underflowConcatWrongLiteral(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const t: "x1e-400" = UnderflowConcat.A;
}

function underflowConcatRuntimeLiteral(): "x0" {
  return UnderflowConcat.A;
}

// #932: an array literal must match one arm of a union of tuples, and cannot
// inhabit a tuple-&-object type it lacks the fields of.
function tupleUnionCross(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const v: [0, 1] | [2, 3] = [0, 3];
}

function tupleAndObject(k: [0, 1] & { foo: string }): string {
  return k.foo;
}

function tupleAndObjectCall(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const s: string = tupleAndObject([0, 1]);
}

// #903: an instanceof hidden type argument must not pool across executions
// through an inferred container.
class PoolBox<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function poolHiddenArgument(items: unknown[]): number {
  const ys = [];
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  for (const x of items) {
    if (x instanceof PoolBox) {
      ys.push(x);
    }
  }
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v;
  }
  return ys.length;
}

// #869: a member refinement must not survive a write through an alias.
function memberRefinementAliasWrite(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    f.x = 99;
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: 1 = e.x;
  }
}

// #840: a captured write to an evolving local is checked, so the local does
// not keep the type of its last visible assignment.
class EvolvingNode {
  value: number = 0;
}

function mkEvolvingNode(): EvolvingNode {
  return new EvolvingNode();
}

function evolvingCapturedWrite(): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  g();
  // @skjs-expect-error Property 'value' does not exist on this type
  const v: number = r.value;
}
