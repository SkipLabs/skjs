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

// With no `default` the switch can match no clause at all, which leaves `y` at
// "a": that path counts too, so `y` is not "b" | "c" here.
function noMatchPathCounts(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      y = c;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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

// FIXME: a branch that always returns never reaches the code after the switch,
// so it should not contribute to the merge — `y` is "c" here. `If` drops such
// branches (isTerminalBlock); the switch does not, so `y` is widened to
// "b" | "c". Pinned to the current (imprecise but sound) behavior.
function returningBranchStillMerged(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      return;
    default:
      y = c;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "c" = y;
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
