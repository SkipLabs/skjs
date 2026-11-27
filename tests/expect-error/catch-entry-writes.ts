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
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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
  const z: "a" = y;
}

// ——— #869: property writes & calls inside try / catch / finally ———
// Member refinements invalidated on a throwing/returning/continuing/re-narrowed
// path inside try or catch must be logged into the try write-log so catch,
// finally, and post-try code see the widened object view.

function aliasWriteBeforeThrowReachesCatch(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      if (c) {
        f.x = 99;
        throw "boom";
      }
    } catch {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function aliasWriteBeforeThrowReachesPostTry(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      if (c) {
        f.x = 99;
        throw "boom";
      }
    } catch {
      // swallow error
    }
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: 1 = e.x;
  }
}

function aliasWriteBeforeReturnReachesFinally(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      if (c) {
        f.x = 99;
        return;
      }
    } finally {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function aliasWriteBeforeContinueReachesFinally(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    for (let i = 0; i < 2; i++) {
      try {
        if (c) {
          f.x = 99;
          continue;
        }
      } finally {
        // @skjs-expect-error Type of value is not assignable to the variable's type annotation
        const z: 1 = e.x;
      }
    }
  }
}

function aliasWriteRenarrowedReachesCatch(mayThrow: () => void): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      f.x = 99;
      mayThrow();
      if (e.x !== 1) return;
    } catch {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function aliasWriteRenarrowedReachesFinally(mayThrow: () => void): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      f.x = 99;
      mayThrow();
      if (e.x !== 1) return;
    } finally {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function callBeforeThrowReachesCatch(c: boolean, mutate: () => void): void {
  const e: { x: number } = { x: 1 };
  if (e.x === 1) {
    try {
      if (c) {
        mutate();
        throw "boom";
      }
    } catch {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function nestedInnerTryAliasWriteEscapesToOuterCatch(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      try {
        if (c) {
          f.x = 99;
          throw "boom";
        }
      } finally {
        // does not suppress the thrown exception
      }
    } catch {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

function nestedInnerFinallyAliasWriteEscapesToOuterCatch(c: boolean): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    try {
      try {
        // nothing
      } finally {
        if (c) {
          f.x = 99;
          throw "boom";
        }
      }
    } catch {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
    }
  }
}

// A pure try without property writes or calls preserves pre-try member
// refinements in catch and finally.
function pureTryPreservesMemberRefinement(): void {
  const e: { x: number } = { x: 1 };
  if (e.x === 1) {
    try {
      const y = 1 + 2;
    } catch {
      const z: 1 = e.x;
    } finally {
      const z2: 1 = e.x;
    }
  }
}

// A property write before throw does not undo a const non-null refinement.
function aliasWriteBeforeThrowPreservesNonNull(c: boolean): void {
  const e: { x: number } | null = { x: 1 };
  const f: { x: number } = { x: 1 };
  if (e !== null) {
    try {
      if (c) {
        f.x = 99;
        throw "boom";
      }
    } catch {
      const g: { x: number } = e;
    } finally {
      const g2: { x: number } = e;
    }
  }
}
