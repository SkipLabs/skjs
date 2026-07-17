// Soundness-boundary pins for isTerminalBlock's continue/break handling
// (TypeCheck.sk, used by If's narrowing merge — see #764). These aren't
// about the false-rejection the fix targets; they pin that the fix does
// NOT overcorrect into wrongly treating a live (non-terminal) branch as
// terminal, which would merge in stale narrowing and let an invalid
// assignment through unflagged.

// A nested loop's own continue must not leak out and make the OUTER
// if-branch appear terminal: the inner loop absorbs it. Both branches of
// the outer if are live, so y stays string | number after it.
function nestedLoopAbsorbsOwnContinue(y: string | number, cond: boolean): void {
  if (cond) {
    for (const x of [1, 2, 3]) {
      if (x === 1) continue;
    }
    y = "reached: the inner loop's continue doesn't propagate out";
  } else {
    y = 42;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: string = y;
}

// A switch does not catch `continue` (only `break`), so a switch whose
// only case continues really is terminal relative to the enclosing if:
// only the else branch's narrowing survives.
function switchContinuePropagatesToLoop(
  y: string | number,
  n: number,
  cond: boolean,
): void {
  for (const _x of [1]) {
    if (cond) {
      switch (n) {
        case 0:
          continue;
        default:
          continue;
      }
      y = "dead code after an always-continuing switch";
    } else {
      y = "reached";
    }
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: number = y;
  }
}

// A `finally` that completes normally doesn't swallow a `continue` from the
// `try` -- the continue still takes effect once finally is done running, so
// the if-branch is still terminal and only the else branch survives.
function tryFinallyContinueStillTerminal(
  y: string | number,
  cond: boolean,
): void {
  for (const _x of [1]) {
    if (cond) {
      try {
        continue;
      } finally {
        // completes normally
      }
      y = "dead code after continue+finally";
    } else {
      y = "reached";
    }
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: number = y;
  }
}

// Both branches terminal (both continue): the merge correctly does nothing
// (conservative no-op) rather than asserting anything about the unreachable
// code after -- which is still type-checked normally, not skipped.
function bothBranchesTerminalStaysConservative(): number {
  for (const x of [1, 2]) {
    if (x === 1) {
      continue;
    } else {
      continue;
    }
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const dead: string = 5;
  }
  return 0;
}

// A write-free break guard narrows like the continue guard does: the branch
// only refines what is already known about v, so only the fall-through
// path's narrowing survives.
function breakGuardNarrowsInSwitch(x: number, v: string | undefined): void {
  switch (x) {
    case 1:
      if (v === undefined) break;
      const s: string = v;
      break;
    default:
      break;
  }
}

// FIXME(#907): a branch that WRITES and then breaks re-joins the flow after
// the enclosing switch with the write live, so dropping its scope loses it:
// f(1, true, ...) reaches z with y === "b" in a variable typed "a". Pinned to
// the current (unsound) acceptance; flipped by the refinement guard.
function writeThenBreakOutOfSwitch(
  x: number,
  c: boolean,
  a: "a",
  b: "b",
): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      if (c) {
        y = b;
        break;
      }
      break;
    default:
      break;
  }
  const z: "a" = y;
}

// FIXME(#907): same through a loop — the continue re-joins at the loop
// header, and the loop can then exit with y === "b".
function writeThenContinueInLoop(c: () => boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  while (c()) {
    if (c()) {
      y = b;
      continue;
    }
  }
  const z: "a" = y;
}
