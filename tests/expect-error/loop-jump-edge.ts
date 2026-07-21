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
  // Pins today's behaviour, which is unsound: the break edge's "b" is lost and
  // this is accepted. The next commit rejects it.
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
  // Pins today's behaviour, which is unsound; the next commit rejects it.
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
  // Pins today's behaviour, which is unsound; the next commit rejects it.
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
  // Pins today's behaviour, which is unsound; the next commit rejects it.
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
  // Pins today's behaviour, which is unsound; the next commit rejects it.
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
  // Pins today's behaviour, which is unsound; the next commit rejects it.
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
