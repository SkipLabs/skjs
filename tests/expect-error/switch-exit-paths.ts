// A switch clause contributes a path out of the switch only when it can reach
// the code after it: by breaking, or — for the last clause — by falling off the
// end. A clause that falls into the next one does not exit there; it runs on,
// and its writes are carried into the clause it falls into (which is the real
// exit). So a falling-through clause is not merged as an independent post-switch
// path, and a break-capable clause is, even if it can also return.

// A `let` with no initializer is definitely assigned after the switch when every
// path out of the switch assigns it. Grouping labels onto one body with an empty
// clause does not add a path that skips the assignment: the empty clause falls
// into the body, it does not leave the switch.
function groupedLabelsDefinitelyAssign(
  x: 1 | 2,
  log: (s: string) => void,
): void {
  let y: string;
  switch (x) {
    case 1:
    case 2:
      y = "set";
      break;
  }
  // @skjs-expect-error Variable 'y' is used before being assigned
  log(y);
}

// Same, but the `default` is the clause that covers the remaining value, so it
// is reached and every path still assigns.
function groupedLabelsWithDefault(
  x: 1 | 2 | 3,
  log: (s: string) => void,
): void {
  let y: string;
  switch (x) {
    case 1:
    case 2:
      y = "set";
      break;
    default:
      y = "def";
  }
  // @skjs-expect-error Variable 'y' is used before being assigned
  log(y);
}

// The guard the fix must keep: when the switch is genuinely not exhaustive and
// has no `default`, matching no clause skips the assignment, so `y` really can
// be read unassigned — this must stay an error.
function notExhaustiveStillErrors(x: number, log: (s: string) => void): void {
  let y: string;
  switch (x) {
    case 1:
    case 2:
      y = "set";
      break;
  }
  // @skjs-expect-error Variable 'y' is used before being assigned
  log(y);
}

// A non-last clause that falls through is not its own way out: it runs on into
// the next clause, whose scope already carries its writes. So a value it leaves
// that the next clause overwrites must not survive to here — `y` is "b" on every
// path out of this switch, not "a" | "b".
function fallthroughClauseIsNotItsOwnExit(x: 1 | 2, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = a;
    case 2:
      y = b;
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "b" = y;
}

// A clause that can break reaches the code after the switch by that break, even
// if it can also return on another path — so its scope is a path out and must be
// merged. Here `y` is "b" via the break, or "a" via the `default`.
function breakOrReturnCountsAsExit(
  x: 1 | 2,
  cond: boolean,
  a: "a",
  b: "b",
): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      y = b;
      if (cond) break;
      return;
    default:
      break;
  }
  // Pins today's behaviour, which is unsound: the break path leaves `y` at "b",
  // so it can reach here as "b", and annotating it "a" must be rejected. Today
  // this clause's scope is dropped (it can also return), so the write is lost
  // and this is wrongly accepted. The next commit rejects it.
  const z: "a" = y;
}
