// A jump edge carries the state at the jump for every binding — including one
// it leaves unassigned: a binding the edge does not mention was left at the
// state above the loop, not at whatever the body's other paths assigned.

// The continue edge leaves `x` unassigned (first iteration with `c` true skips
// the assignment), and the increment runs on that path: `i + x` is
// `i + undefined` at runtime.
function continueLeavesUnassigned(c: boolean): void {
  let x: number;
  // Pins today's behaviour, which is unsound: the edge mentions nothing for
  // `x`, so the fold before the increment keeps the body-end "assigned" state
  // and the read passes. The next commit rejects it.
  for (let i = 0; i < 3; i = i + x) {
    if (c) {
      continue;
    }
    x = 1;
  }
}

// Assigned before the loop: the edge's implicit state for `x` is already
// initialized, so the increment's read is fine.
function assignedBeforeTheLoop(c: boolean): void {
  let x: number = 0;
  for (let i = 0; i < 3; i = i + x) {
    if (c) {
      continue;
    }
    x = 1;
  }
}

// Assigned before the jump: the edge carries the assignment itself.
function assignedBeforeTheJump(c: boolean): void {
  let x: number;
  for (let i = 0; i < 3; i = i + x) {
    x = 2;
    if (c) {
      continue;
    }
    x = 1;
  }
}
