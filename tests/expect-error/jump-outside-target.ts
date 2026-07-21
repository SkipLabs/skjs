// A `break` or `continue` must have a target: an enclosing loop (or switch,
// for `break`) in the same function. A jump with none is a JavaScript
// SyntaxError at load time — and one inside a lambda cannot take an enclosing
// function's loop as its target either (tsc reports TS1107 for both).

// Pins today's behaviour, which reports nothing on any of these; the next
// commit rejects them all.

function breakWithNoTarget(): void {
  break;
}

function continueWithNoTarget(): void {
  continue;
}

// A switch catches `break`, but not `continue`: with no enclosing loop this
// continue has no target.
function continueInSwitchWithNoLoop(x: number): void {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  switch (x) {
    case 1:
      continue;
  }
}

// The enclosing loop is beyond the lambda's function boundary, so it is not a
// valid target — the jump must not be routed to it.
function breakInLambdaInLoop(c: boolean): void {
  while (c) {
    const f = (): void => {
      break;
    };
    f();
  }
}

function continueInLambdaInLoop(c: boolean): void {
  while (c) {
    const f = (): void => {
      continue;
    };
    f();
  }
}
