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

// A tuple-shaped object (the expanded constraint of K) renders as the tuple
// it denotes, not as the object form listing every array method.
// FIXME: TypeScript accepts this call (K = [0, 1]); the array literal
// commits to the widened tuple before the constraint check (case 2a'), so
// SKJS rejects it -- and in the CLI output the rescued pair renders both
// sides as the committed type, reading as a tautology.
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type [unknown, unknown]
  // @skjs-expect-error-line3 is not assignable to type ['0', '1']
  const r = g2([0, 1]);
}

// A genuinely mismatched operand gets the readable pair.
declare function fk<K extends [0, 1]>(x: K): K;
function nonTupleOperand(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type ['0', '1']
  const r = fk(5);
}
