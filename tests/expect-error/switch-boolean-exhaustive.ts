// `true` and `false` are all a boolean can be, so handling both leaves no value
// unmatched — the same as covering a union of literals, which is what a boolean
// with neither ruled out is.

// Both values are handled and both clauses return, so this returns on every
// path.
function bothValuesReturn(b: boolean): number {
  switch (b) {
    case true:
      return 1;
    case false:
      return 0;
  }
}

// `y` is assigned by every clause that can be taken, so it is never left at "a".
function bothValuesAssign(bo: boolean, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (bo) {
    case true:
      y = b;
      break;
    case false:
      y = c;
      break;
  }
  const z: "b" | "c" = y;
}

// With both values handled, a `default` can never be taken.
function defaultAfterBothValues(b: boolean): void {
  switch (b) {
    case true:
      break;
    case false:
      break;
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    default:
      break;
  }
}

// Handling one value leaves the other, exactly as a missing case does for a
// union of literals.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function onlyOneValue(b: boolean): number {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  // @skjs-expect-warning Switch is not exhaustive; the following cases are unhandled
  switch (b) {
    case true:
      return 1;
  }
}

// Covering both values is not enough if a clause escapes rather than returns.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function bothValuesButOneBreaks(b: boolean): number {
  switch (b) {
    case true:
      break;
    case false:
      return 0;
  }
}
