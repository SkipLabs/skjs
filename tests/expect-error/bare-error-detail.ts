// Error-detail rendering shapes for subtype failures (issue #672).

// Both sides are pure type parameters (no insts), so no frame renders a
// clause pair; the fall-back prints the type pair, anchored at the type
// parameters' declarations.
function id2<T, U>(x: T): U {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type 'T'
  // @skjs-expect-error-line3 is not assignable to type 'U'
  return x;
}

// K's expanded constraint renders as the tuple it denotes, not as the
// object form listing every array method.
// FIXME: TypeScript accepts this call (K = [0, 1]); the array literal
// commits to the widened tuple before the constraint check (case 2a'), so
// SKJS rejects it.
// FIXME: both sides below print as '[0, 1]', so the message cannot explain
// the rejection -- the rendered source is not the type the check rejected
// (#914). The pair is pinned as-is: it is what a user sees.
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 1]'
  // @skjs-expect-error-line3 is not assignable to type '[0, 1]'
  const r = g2([0, 1]);
}

// A genuinely mismatched operand gets the readable pair.
declare function fk<K extends [0, 1]>(x: K): K;
function nonTupleOperand(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type '[0, 1]'
  const r = fk(5);
}

// Primitive literals render as TypeScript source syntax: the numeric literal
// type bare (`1`), the string literal type double-quoted (`"1"`), keeping the
// two sides of the mismatch distinguishable.
function indistinguishableLiteralKinds(x: 1): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '1'
  // @skjs-expect-error-line3 is not assignable to type '"1"'
  const y: "1" = x;
}

// An intersection with an extra member: the object form shows `foo` -- the
// member the failure is actually about -- and must keep doing so.
declare function hx<K extends [0, 1] & { foo: string }>(x: K): K;
function extraMemberShown(): void {
  const arg: [0, 1] = [0, 1];
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 1]'
  // @skjs-expect-error-line3 is not assignable to type {
  const r = hx(arg);
}

// A readonly tuple expansion renders as the readonly tuple it is.
declare function gr<K extends readonly [0, 1]>(x: K): K;
function readonlyTupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 2]'
  // @skjs-expect-error-line3 is not assignable to type 'readonly [0, 1]'
  const r = gr([0, 2]);
}
