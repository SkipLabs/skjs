// After a switch, a binding's type must be the union over every path that can
// reach that point: each branch, plus — when there is no `default` — matching
// no clause at all, which leaves the binding untouched.

// Every branch contributes to the merge, including the ones in between: `y` is
// "b" when x === 2, so it is not "a" | "c" here.
function middleBranchNotDropped(x: 1 | 2 | 3, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = a;
      break;
    case 2:
      y = b;
      break;
    case 3:
      y = c;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "a" | "c" = y;
}

// FIXME: with no `default` the switch can match no clause at all, leaving `y`
// as "a", but that path is dropped from the merge. Pinned to the current
// (unsound) behavior; fixed in a later commit.
function noMatchPathDropped(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      y = c;
      break;
  }
  const z: "b" | "c" = y;
}

// A `default` covers every unmatched value, so no untouched path remains and
// the merge stays precise: `y` is exactly "b" | "c" here.
function withDefaultStaysPrecise(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      break;
    default:
      y = c;
      break;
  }
  const z: "b" | "c" = y;
}

// A binding not assigned in the first branch already merges correctly (it takes
// `merge`'s Left/Right arm, which accumulates through the parent scope).
function notAssignedInFirstBranch(x: 1 | 2 | 3, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      break;
    case 2:
      y = b;
      break;
    case 3:
      y = c;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "a" | "c" = y;
}
