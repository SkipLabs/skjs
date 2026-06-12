// Error-detail fall-backs for subtype failures (issue #672).

// Both sides are pure type parameters (no insts), so the default detail level
// renders no clause pairs.
// FIXME: prints bare -- only the headline, with no type pair explaining the
// failure.
function id2<T, U>(x: T): U {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// The rescued pair prints K's expanded constraint, the object form of the
// tuple [0, 1], listing every array method.
// FIXME: should render as the tuple it is, not the expanded object form.
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type [unknown, unknown]
  // @skjs-expect-error-line3 is not assignable to type {
  const r = g2([0, 1]);
}
