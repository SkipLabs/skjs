// Error-detail rendering shapes for subtype failures (issue #672).

// Both sides are pure type parameters (no insts), so no frame renders a
// clause pair; the fall-back prints the type pair, anchored at the type
// parameters' declarations.
function id2<T, U>(x: T): U {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type T
  // @skjs-expect-error-line3 is not assignable to type U
  return x;
}

// The rescued pair prints K's expanded constraint, the object form of the
// tuple [0, 1], listing every array method.
// FIXME: should render as the tuple it is. TypeScript also accepts this call
// (K = [0, 1]); the array literal commits to the widened tuple before the
// constraint check (case 2a'), so SKJS rejects it.
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type [unknown, unknown]
  // @skjs-expect-error-line3 is not assignable to type {
  const r = g2([0, 1]);
}

// A genuinely mismatched operand: same expanded object form for the
// constraint side.
// FIXME: should render as the tuple it is.
declare function fk<K extends [0, 1]>(x: K): K;
function nonTupleOperand(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type {
  const r = fk(5);
}

// An intersection with an extra member: the object form shows `foo` -- the
// member the failure is actually about -- and must keep doing so.
declare function hx<K extends [0, 1] & { foo: string }>(x: K): K;
function extraMemberShown(): void {
  const arg: [0, 1] = [0, 1];
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type ['0', '1']
  // @skjs-expect-error-line3 is not assignable to type {
  const r = hx(arg);
}

// A readonly tuple expansion: the object form shows the readonly markers.
// FIXME: should render as the readonly tuple it is.
declare function gr<K extends readonly [0, 1]>(x: K): K;
function readonlyTupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type [unknown, unknown]
  // @skjs-expect-error-line3 is not assignable to type {
  const r = gr([0, 2]);
}
