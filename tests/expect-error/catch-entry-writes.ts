// An exception can leave a `try` after any prefix of it, so its `catch` (and
// `finally`) is entered with each binding at any value the try wrote — not
// just the value the try ended on. The entry state unions every write made
// while the try ran.

// Pins today's behaviour, which is unsound (SkipLabs/skjs#963): the write
// `y = b` is overwritten by the try's end, so only the end state reaches the
// catch, and `z: "a" = y` is accepted — while `mayThrow()` throwing leaves
// `y` at "b". The next commit rejects it, and its finally and nested-try
// variants.

function midTryWriteReachesCatch(a: "a", b: "b", mayThrow: () => void): void {
  let y: "a" | "b" = a;
  y = a;
  try {
    y = b;
    mayThrow();
    y = a;
  } catch {
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
    const z: "a" = y;
  }
}

// The outer catch sees the inner try's writes too — the exception can leave
// both after any prefix — even when the inner construct fully cleans up its
// own end state.
function innerTryWriteReachesOuterCatch(
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
