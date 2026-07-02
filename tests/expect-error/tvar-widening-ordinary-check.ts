// Known issue (false positive): SKJS rejects these programs, but tsc accepts
// them (except testTwoArgUnion, noted below).
//
// A covariant check of an already-determined inference candidate against a
// wider expected type widens the candidate: passing `a` (solved to a narrow
// type) to a parameter of a wider union type folds the parameter type into
// the candidate via union at the covariant grow site, so a later use of `a`
// sees the whole union. This is the ordinary-call counterpart of
// tvar-widening-in-constraint-check.ts -- no `extends` constraint is
// involved, so the freezeCandidates guard of #713 does not apply. A correct
// fix must make #713's no-widening rule an unconditional invariant of the
// covariant grow write site.

function id_oc<X>(x: X): X {
  return x;
}
function g_oc(x: number | string): void {}
function gObj_oc(x: { x: string } | number): void {}
function makeArr_oc<T>(x: T): T[] {
  return [x];
}

function testConstCandidate(): number {
  const a = id_oc(1);
  g_oc(a);
  // FIXME: remove this annotation once the widening is fixed; tsc accepts this.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return a;
}

function testLetCandidate(): number {
  let a = id_oc(1);
  g_oc(a);
  // FIXME: remove this annotation once the widening is fixed; tsc accepts this.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return a;
}

function testObjectCandidate(): string {
  const a = id_oc({ x: "s" });
  gObj_oc(a);
  // FIXME: remove this annotation once the widening is fixed; tsc accepts
  // this. `a` is widened to { x: string } | number, so the property access
  // fails on the number branch.
  // @skjs-expect-error Property 'x' does not exist on this type
  return a.x;
}

// An unbound candidate may still take the expected type as its value, and a
// fresh generic result still adapts to a wider expected type at an invariant
// position via the contravariant grow direction.
function testAdaptiveInvariant(): Array<number | string> {
  const a = makeArr_oc(1);
  return a;
}

// A candidate nested inside another candidate's value: the wide check on the
// outer value must not leak into the inner candidate through structural
// descent.
declare class Box_oc<T> {
  v: T;
}
declare function mkBox_oc<T>(x: T): Box_oc<T>;
declare function useWideBox_oc(b: Box_oc<number | string>): void;
function testNestedCandidate(): number {
  const a = id_oc(1);
  const b = mkBox_oc(a);
  // FIXME: remove this annotation once the widening is fixed; tsc accepts
  // this. The widening leaks through structural descent into `a`'s
  // candidate, and the invariant field check then fails.
  // @skjs-expect-error Argument is not assignable to the parameter's type
  useWideBox_oc(b);
  return a;
}

// Lower-bound union growth across arguments is unaffected. (tsc infers T from
// the first argument and rejects the second; SKJS's union growth soundly
// accepts with T = number | string -- pre-existing behavior, pinned here so
// the no-widening rule is not over-extended to contravariant grow sites.)
function two_oc<T>(x: T, y: T): T[] {
  return [x, y];
}
function testTwoArgUnion(): Array<number | string> {
  return two_oc(1, "a");
}
