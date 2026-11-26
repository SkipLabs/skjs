// A `break` or `continue` leaves the loop body mid-block carrying the state at
// the jump — which a later write in the body can change, so the state after the
// loop is the union of the normal exits and every jump edge, not just the
// body's end-of-block state.

// The break edge leaves with `y === "b"`; the body's end overwrites to "a", so
// only the edge still carries the "b" out. `whileBreakEdge(true, true, …)`
// leaves `y` at "b".
function whileBreakEdge(c: boolean, d: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    if (d) {
      y = b;
      break;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z1: "a" = y;
}

// A `continue` re-enters the header, whose exit (the condition turning false)
// then leaves the loop with the continue edge's state: `y === "b"` escapes the
// same way.
function whileContinueEdge(c: boolean, d: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    if (d) {
      y = b;
      continue;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z2: "a" = y;
}

// The same two edges in a `for`. The break path skips the increment; the
// continue path runs it.
function forBreakEdge(d: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  for (let i = 0; i < 3; i = i + 1) {
    if (d) {
      y = b;
      break;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z3: "a" = y;
}

function forContinueEdge(d: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  for (let i = 0; i < 3; i = i + 1) {
    if (d) {
      y = b;
      continue;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z4: "a" = y;
}

// And in a `for … of`.
function forOfBreakEdge(xs: number[], a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  for (const v of xs) {
    if (v > 0) {
      y = b;
      break;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z5: "a" = y;
}

// The value at the jump is what counts, and only that: a break that carries
// nothing new does not widen the state after the loop.
function guardStaysGreen(c: boolean, d: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    if (d) {
      break;
    }
    y = b;
  }
  const z6: "a" | "b" = y;
}

// A `break` in a switch inside the loop leaves the switch, not the loop: the
// body still ends by overwriting `y`, so nothing but "a" reaches the code
// after the loop, and binding it there stays accepted.
function breakInSwitchBindsToTheSwitch(
  x: number,
  c: boolean,
  a: "a",
  b: "b",
): void {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
    switch (x) {
      case 1:
        y = b;
        break;
    }
    y = a;
  }
  const z7: "a" = y;
}

// A `continue` in that switch leaves the loop iteration instead — skipping the
// overwrite — so its edge does reach the code after the loop.
function continueInSwitchBindsToTheLoop(
  x: number,
  c: boolean,
  a: "a",
  b: "b",
): void {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
    switch (x) {
      case 1:
        y = b;
        continue;
    }
    y = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z8: "a" = y;
}

// A `break` in a loop inside a switch clause leaves the loop, not the switch:
// the clause then overwrites `y`, so only "a" leaves the switch.
function breakInLoopBindsToTheLoop(
  x: number,
  c: boolean,
  a: "a",
  b: "b",
): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      while (c) {
        y = b;
        break;
      }
      y = a;
      break;
    default:
      break;
  }
  const z9: "a" = y;
}

// SkipLabs/skjs#968 — a `continue` re-enters the loop header, so the header's
// effects apply to the folded edge state, not only to the pre-body entry:
// its writes run again before the loop can exit through that re-entry, and
// its test is checked against values the edge can carry.
type LoopHeaderN = { go(): boolean };

// The header test sees the continue edge's value: `x` is null on that edge,
// so `x.go()` in the header is rejected (tsc: 'x' is possibly 'null').
function whileHeaderTestSeesTheContinueEdge(c: boolean, n: LoopHeaderN): void {
  let x: LoopHeaderN | null = null;
  x = n;
  // @skjs-expect-error Property access is not allowed on this type
  while (x.go()) {
    if (c) {
      x = null;
      continue;
    }
    x = n;
  }
}

function forHeaderTestSeesTheContinueEdge(c: boolean, n: LoopHeaderN): void {
  let x: LoopHeaderN | null = null;
  x = n;
  // @skjs-expect-error Property access is not allowed on this type
  for (let i = 0; x.go(); i = i + 1) {
    if (c) {
      x = null;
      continue;
    }
    x = n;
  }
}

// The header's write `(x = a)` runs again on the continue edge, so the edge's
// "b" is overwritten before the loop can exit through it (tsc accepts).
function whileHeaderWriteReRunsOnContinueEdge(
  d: boolean,
  a: "a",
  b: "b",
): void {
  let x: "a" | "b" = a;
  x = a;
  while ((x = a) !== "a") {
    if (d) {
      x = b;
      continue;
    }
    x = a;
  }
  const y: "a" = x;
}

// The entry path exits through the header as well: its write has run before
// the first test can turn false (tsc accepts).
function whileHeaderWriteRunsOnTheEntryExit(a: "a", b: "b"): void {
  let x: "a" | "b" = b;
  while ((x = a) !== "a") {}
  const y: "a" = x;
}

// Same in a `for`: a continue edge runs the increment, then the header.
function forHeaderWriteReRunsOnContinueEdge(d: boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  for (let i = 0; (x = a) !== "a"; i = i + 1) {
    if (d) {
      x = b;
      continue;
    }
    x = a;
  }
  const y: "a" = x;
}

function forHeaderWriteRunsOnTheEntryExit(a: "a", b: "b"): void {
  let x: "a" | "b" = b;
  for (let i = 0; (x = a) !== "a"; i = i + 1) {}
  const y: "a" = x;
}

// A `break` skips the header, so its edge's "b" does reach the code after the
// loop (tsc rejects too) — the header write must not overwrite a break edge.
function whileBreakSkipsTheHeaderWrite(d: boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  while ((x = a) !== "a") {
    if (d) {
      x = b;
      break;
    }
    x = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

// With a header increment write, the increment already re-runs on the
// continue edge, so the exit is "a" (tsc agrees).
function forIncrementWriteReRunsOnContinueEdge(
  d: boolean,
  a: "a",
  b: "b",
): void {
  let x: "a" | "b" = a;
  for (x = a; (x = a) !== "a"; x = a) {
    if (d) {
      x = b;
      continue;
    }
    x = a;
  }
  const y: "a" = x;
}
