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

// A branch that always returns never reaches the code after the switch, so it
// is not one of the paths merged into it: `y` is exactly "c" here.
function returningBranchNotMerged(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      return;
    default:
      y = c;
      break;
  }
  const z: "c" = y;
}

// ... but a branch that merely breaks is a path out, and still counts.
function breakingBranchMerged(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      break;
    default:
      y = c;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "c" = y;
}

// Every branch returns, so none of them is a path out and the merge is handed
// no scopes at all. The only way to reach the code below is matching no clause,
// which leaves `y` exactly as it was — so it stays "a" rather than widening.
function allBranchesTerminal(x: number, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  y = a;
  switch (x) {
    case 1:
      y = b;
      return;
    case 2:
      y = c;
      return;
  }
  const z: "a" = y;
}

// ... and with a `default` there is no untouched path either, so the merge gets
// nothing at all to do and the code after the switch is unreachable.
function allBranchesTerminalWithDefault(x: number): number {
  switch (x) {
    case 1:
      return 1;
    default:
      return 2;
  }
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

const switchSeed: number = 1;
function switchLaterBinding(tag: number): number {
  switch (tag) {
    case 0:
      return switchSeed;
    default: {
      const switchSeed = 2;
      return switchSeed;
    }
  }
}
function switchSharedBinding(tag: number): number {
  switch (tag) {
    case 0:
      // @ts-expect-error Variable 'switchSeed' is used before being assigned
      return switchSeed;
    default:
      const switchSeed = 2;
      return switchSeed;
  }
}

function switchLabelBinding(tag: number): number {
  switch (tag) {
    // @ts-expect-error Variable 'switchSeed' is used before being assigned
    case switchSeed:
      return 1;
    default:
      const switchSeed = 2;
      return switchSeed;
  }
}
