// A `break` or `continue` must have a target: an enclosing loop (or switch,
// for `break`) in the same function. A jump with none is a JavaScript
// SyntaxError at load time — and one inside a lambda cannot take an enclosing
// function's loop as its target either (tsc reports TS1107 for both).

function breakWithNoTarget(): void {
  // @skjs-expect-error Jump target cannot cross function boundary
  break;
}

function continueWithNoTarget(): void {
  // @skjs-expect-error Jump target cannot cross function boundary
  continue;
}

// A switch catches `break`, but not `continue`: with no enclosing loop this
// continue has no target.
function continueInSwitchWithNoLoop(x: number): void {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  switch (x) {
    case 1:
      // @skjs-expect-error Jump target cannot cross function boundary
      continue;
  }
}

// The enclosing loop is beyond the lambda's function boundary, so it is not a
// valid target — the jump must not be routed to it.
function breakInLambdaInLoop(c: boolean): void {
  while (c) {
    const f = (): void => {
      // @skjs-expect-error Jump target cannot cross function boundary
      break;
    };
    f();
  }
}

function continueInLambdaInLoop(c: boolean): void {
  while (c) {
    const f = (): void => {
      // @skjs-expect-error Jump target cannot cross function boundary
      continue;
    };
    f();
  }
}

// A loop inside the lambda is a valid target for the lambda's own jumps.
function loopInLambdaInLoop(c: boolean): void {
  while (c) {
    const f = (): void => {
      while (c) {
        break;
      }
    };
    f();
  }
}
