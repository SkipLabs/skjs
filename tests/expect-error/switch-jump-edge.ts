// A `break` leaves the switch carrying the state at the jump — which a later
// write in the same clause can change, so the state after the switch is the
// union over every break edge, not just each clause's end-of-block state.

// The `break` under `if (c)` leaves with `y === "a"`; the fall-through path then
// writes `y = "b"` and breaks with `y === "b"`. So after the switch `y` is
// "a" | "b", and `z: "b"` must be rejected — `inst1(1, true, …)` leaves `y` at
// "a".
function midBreakEdgeCounts(x: number, c: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      if (c) {
        break;
      }
      y = b;
      break;
    default:
      y = b;
      break;
  }
  // Pins today's behaviour, which is unsound: the `break` under `if (c)` leaves
  // `y` at "a", so `z: "b"` can be reached with `y === "a"`, yet this is
  // accepted — the break edge's state is not carried to the code after the
  // switch. The next commit rejects it.
  const z: "b" = y;
}

// The value at the break edge is what counts: here every edge leaves `y` at "b"
// or "a", and assigning to that union is accepted.
function midBreakEdgeAccepted(x: number, c: boolean, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      if (c) {
        break;
      }
      y = b;
      break;
    default:
      y = b;
      break;
  }
  const z: "a" | "b" = y;
}

// A plain break at the end of each clause is unchanged: `y` after the switch is
// the union of what each clause left.
function endBreakUnchanged(x: 1 | 2, a: "a", b: "b", c: "c"): void {
  let y: "a" | "b" | "c" = a;
  y = a;
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      y = c;
      break;
  }
  const z: "a" | "b" | "c" = y;
}
