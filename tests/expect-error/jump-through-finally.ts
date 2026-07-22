// A jump that leaves a `try` runs its `finally` on the way out, so the state
// the edge carries to the jump's target is the state *after* the finally — a
// write there is on every such path.

// (tsc accepts the first four — its finally handling shares the hole it had
// here — but the runtime witness is concrete, and SKJS's diagnostics answer
// to the runtime, not to tsc.)

function breakThroughFinally(c: () => boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  x = a;
  while (c()) {
    if (c()) {
      try {
        break;
      } finally {
        x = b;
      }
    }
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

function continueThroughFinally(c: () => boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  x = a;
  while (c()) {
    if (c()) {
      try {
        continue;
      } finally {
        x = b;
      }
    }
    x = a;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

function breakOutOfSwitchThroughFinally(n: number, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  x = a;
  switch (n) {
    case 1:
      try {
        break;
      } finally {
        x = b;
      }
    default:
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

// A conditional write in the finally leaves both outcomes possible on the
// edge: the write, or the state at the jump.
function conditionalFinallyWrite(c: () => boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  x = a;
  while (c()) {
    if (c()) {
      try {
        break;
      } finally {
        if (c()) {
          x = b;
        }
      }
    }
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

// The finally applies to a jump from the `catch` block too.
function jumpFromCatchThroughFinally(
  c: () => boolean,
  mayThrow: () => void,
  a: "a",
  b: "b",
): void {
  let x: "a" | "b" = a;
  x = a;
  while (c()) {
    try {
      mayThrow();
    } catch {
      break;
    } finally {
      x = b;
    }
  }
  // Already rejected today: the no-throw path runs the finally too, so the
  // write reaches the body's end and the ordinary loop merge. The edge fix
  // must keep it rejected.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: "a" = x;
}

// A jump recorded before the try is not the finally's business: the edge left
// the loop before the try was ever entered.
function jumpBeforeTheTryIsUntouched(c: () => boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  x = a;
  while (c()) {
    if (c()) {
      break;
    }
    try {
      x = a;
    } finally {
      x = a;
    }
  }
  const y: "a" = x;
}
