// Error-detail fall-backs for subtype failures (issue #672).

// Both sides are pure type parameters (no insts), so no frame renders a
// clause pair; the fall-back prints the outermost type pair, anchored at the
// type parameters' declarations.
function id2<T, U>(x: T): U {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type T:2:828896151461914054
  // @skjs-expect-error-line3 is not assignable to type U:3:828896151461914054
  return x;
}

// K's expanded constraint carries the array methods, so it keeps the
// (truthful) object form; only a TFields holding nothing beyond the tuple
// shape renders as a tuple.
// FIXME: TypeScript accepts this call (K = [0, 1]); the array literal
// commits to the widened tuple before the constraint check (case 2a'), so
// SKJS rejects it.
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type [unknown, unknown]
  // @skjs-expect-error-line3 is not assignable to type {
  const r = g2([0, 1]);
}

// A genuinely mismatched operand gets the pair (the constraint side keeps
// the object form, which carries the array methods).
declare function fk<K extends [0, 1]>(x: K): K;
function nonTupleOperand(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type {
  const r = fk(5);
}

// Guards: the tuple shorthand never hides a member. An intersection's extra
// member keeps the object form, which shows `foo` -- the member the failure
// is actually about.
declare function hx<K extends [0, 1] & { foo: string }>(x: K): K;
function extraMemberShown(): void {
  const arg: [0, 1] = [0, 1];
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type ['0', '1']
  // @skjs-expect-error-line3 is not assignable to type {
  const r = hx(arg);
}

// A readonly tuple expansion keeps the object form, which shows the
// readonly markers.
declare function gr<K extends readonly [0, 1]>(x: K): K;
function readonlyMarkersShown(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line3 is not assignable to type {
  const r = gr([0, 2]);
}
