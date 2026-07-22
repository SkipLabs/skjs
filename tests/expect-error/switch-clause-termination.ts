// A clause's termination is the checked walk's answer — the same one that
// decides whether the function returns — so a clause that cannot complete
// normally is treated as terminal everywhere it matters. The old separate
// walker judged a clause before checking it, when a nested exhaustive
// no-default switch was not yet known to be exhaustive, and mis-judged such a
// clause as may-fall-through: reporting a fallthrough that cannot happen, and
// merging a phantom path into the scope after the switch.

// The `case true` clause always returns through the inner exhaustive switch,
// so it does not fall into `case false` — no fallthrough to report — and the
// function returns on every path.
function clauseEndingInExhaustiveSwitch(x: 0 | 1, y: boolean): number {
  switch (y) {
    case true:
      switch (x) {
        case 0:
          return 1;
        case 1:
          return 2;
      }
    case false:
      return 3;
  }
}

// The `case 1` clause always returns, so the only path out of the switch is
// `case 0`'s break: `v` is exactly "a" after it, and the string call is legal.
// (The phantom may-fall-through path used to push `v = 42` into the merge and
// reject this.)
function terminalLastClauseLeavesNoPath(x: 0 | 1, y: 0 | 1): string {
  let v: string | number = "init";
  switch (x) {
    case 0:
      v = "a";
      break;
    case 1:
      v = 42;
      switch (y) {
        case 0:
          return "r0";
        case 1:
          return "r1";
      }
  }
  return v.toUpperCase();
}

// The same precision cuts the other way: `v` cannot be 42 here, and the dead
// comparison is called out.
function deadComparisonAfterTerminalClause(x: 0 | 1, y: 0 | 1): void {
  let v: string | number = "init";
  switch (x) {
    case 0:
      v = "a";
      break;
    case 1:
      v = 42;
      switch (y) {
        case 0:
          return;
        case 1:
          return;
      }
  }
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  if (v === 42) {
    console.log("num");
  }
}
