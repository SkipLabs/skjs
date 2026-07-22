// An exception can leave a `try` after any prefix of it, so its `catch` (and
// `finally`) is entered with each binding at any value the try wrote — not
// just the value the try ended on. The entry state unions every write made
// while the try ran, as tsc's does.

function midTryWriteReachesCatch(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    mayThrow();
    y = a;
  } catch {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

function midTryWriteReachesFinally(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    mayThrow();
    y = a;
  } finally {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

// An inner try whose catch absorbs every exception — and cannot itself throw
// — keeps its intermediate states to itself: no path carries the inner "b" to
// the outer catch, which tsc agrees on.
function absorbedInnerTryDoesNotEscape(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    try {
      y = b;
      mayThrow();
      y = a;
    } catch {
      y = a;
    }
    mayThrow();
  } catch {
    const z: "a" = y;
  }
}

// But a catch that can itself throw lets the exception escape carrying the
// inner try's states: the rethrow happens with `y` still at whatever the
// inner try wrote. (tsc accepts this one — its catch entries are not
// compositional — but the runtime witness is concrete, and the diagnostics
// answer to the runtime.)
function rethrowingInnerCatchEscapes(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    try {
      y = b;
      mayThrow();
      y = a;
    } catch {
      mayThrow();
      y = a;
    }
  } catch {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

// A write the try ends on reaches the catch through the ordinary merge
// already — stays rejected.
function endOfTryWriteReachesCatch(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    mayThrow();
  } catch {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

// A catch's own write reaches the finally — it may throw mid-way too.
function catchWriteReachesFinally(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    mayThrow();
  } catch {
    y = b;
    mayThrow();
  } finally {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

// A try's writes are its own: a later, separate try's catch is entered after
// the first try fully resolved, where `y` is back to "a" on every path.
function separateTryDoesNotLeak(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    y = a;
  } catch {
    y = a;
  }
  try {
    mayThrow();
  } catch {
    const z: "a" = y;
  }
}

// A binding local to the try is out of scope in the catch; writing it must
// not confuse the entry state.
function tryLocalWriteIsInvisible(a: "a", b: "b", mayThrow: () => void): void {
  try {
    let t: "a" | "b" = a;
    t = b;
    mayThrow();
  } catch {
    const z: "a" = a;
  }
}

// A mid-try assignment does not make the catch read the binding as assigned:
// the throw may come first.
function midTryAssignmentIsNotDefinite(
  mayThrow: () => void,
  log: (n: number) => void,
): void {
  let y: number;
  try {
    y = 1;
    mayThrow();
  } catch {
    // @skjs-expect-error Variable 'y' is used before being assigned
    log(y);
  }
}

// ——— Escape channels beyond the plain shapes ———

// A finally's write leaves with an exception passing THROUGH it, not only
// with one it throws itself: the inner try's exception runs the inner finally
// on the way out, and arrives at the outer catch with the write applied.
function passingExceptionCarriesFinallyWrite(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    try {
      mayThrow();
    } finally {
      y = b;
    }
    mayThrow();
    y = a;
  } catch {
    const z: "a" = y;
  }
}

// A value that outlives an absorbed inner construct normally is in flight in
// the outer try: a later throw carries it to the outer catch, however calmly
// the inner construct resolved.
function survivorCarriedByLaterThrow(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    try {
      y = b;
      mayThrow();
      y = a;
    } catch {}
    mayThrow();
    y = a;
  } catch {
    const z: "a" = y;
  }
}

// A return unwinds through every enclosing finally, carrying the catch's
// state — seeds included. Rejected before and after the next commit, but the
// channel changes: today it leans on the returning catch's state leaking into
// the ordinary merge; the fix routes the unwind explicitly and removes the
// leak.
function returnUnwindsThroughOuterFinally(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    try {
      y = b;
      mayThrow();
      y = a;
    } catch {
      return;
    }
  } finally {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: "a" = y;
  }
}

// But a catch that never completes normally is no part of the flow AFTER the
// construct: code there runs only when the try completed, ending on `y = a`.
// Pins today's behaviour, which wrongly merges the returning catch's seeded
// state into the code after; the next commit accepts this.
function returningCatchLeavesThePostFlowAlone(
  a: "a",
  b: "b",
  mayThrow: () => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    mayThrow();
    y = a;
  } catch {
    return;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "a" = y;
}
