// Loop-exit narrowing for `while` and `for` conditions (SkipLabs/skjs#707).
//
// Normal loop exit happens only after the loop condition evaluates to false, so
// the false-branch narrowing of the condition holds after the loop unless a
// `break` bypasses the header test or the condition is unstable (writes or
// effects invalidating its reads).

// --- Positive cases: normal exit narrows on the condition being false ---

function whileNotNullExit(x: string | null): null {
  while (x !== null) {
    x = null;
  }
  return x;
}

function whileEqNullExit(x: string | null): string {
  while (x === null) {
    x = "ok";
  }
  return x;
}

function whileOrExit(x: 1 | 2 | 3, three: 3): 3 {
  while (x === 1 || x === 2) {
    x = three;
  }
  return x;
}

function whileTypeofExit(x: string | number): number {
  while (typeof x === "string") {
    x = 1;
  }
  return x;
}

function whileDiscriminatedUnionExit(
  s: { kind: "a"; a: number } | { kind: "b"; b: string },
): string {
  while (s.kind === "a") {
    s = { kind: "b", b: "done" };
  }
  return s.b;
}

function whileMemberNotNullExit(o: { v: string | null }): null {
  while (o.v !== null) {
    o.v = null;
  }
  return o.v;
}

function whileWithCallInBodyExit(
  x: string | null,
  step: () => string | null,
): null {
  while (x !== null) {
    x = step();
  }
  return x;
}

function whileMemberWithCallInBodyExit(
  o: { v: string | null },
  step: (box: { v: string | null }) => void,
): null {
  while (o.v !== null) {
    step(o);
  }
  return o.v;
}

function whileWithContinueExit(
  x: string | null,
  skip: boolean,
  step: () => string | null,
): null {
  while (x !== null) {
    if (skip) {
      x = step();
      continue;
    }
    x = null;
  }
  return x;
}

function whileWithReturnInBodyExit(x: string | null, done: boolean): null {
  while (x !== null) {
    if (done) {
      return null;
    }
    x = null;
  }
  return x;
}

function whileBreakAlsoNarrows(x: "go" | "stop" | null): "stop" | null {
  while (x !== null) {
    if (x === "stop") {
      break;
    }
    x = null;
  }
  return x;
}

function whileBreakAssignsSameAsExit(x: string | null, flag: boolean): null {
  while (x !== null) {
    if (flag) {
      x = null;
      break;
    }
    x = null;
  }
  return x;
}

function whileCapturedMutatedByBodyCallExit(
  step: () => void,
  init: string | null,
): null {
  let x: string | null = init;
  const reset = (): void => {
    x = null;
  };
  while (x !== null) {
    step();
    reset();
  }
  return x;
}

function forNotNullExit(x: string | null, next: () => string | null): null {
  for (; x !== null; x = next()) {
    const s: string = x;
  }
  return x;
}

function forDiscriminatedUnionExit(
  s: { kind: "a"; a: number } | { kind: "b"; b: string },
  step: () => { kind: "a"; a: number } | { kind: "b"; b: string },
): string {
  for (; s.kind === "a"; s = step()) {
    const n: number = s.a;
  }
  return s.b;
}

function forBreakAlsoNarrows(
  x: "go" | "stop" | null,
  next: () => "go" | "stop" | null,
): "stop" | null {
  for (; x !== null; x = next()) {
    if (x === "stop") {
      break;
    }
  }
  return x;
}

// --- Negative / soundness-boundary cases (must remain rejected) ---

// A `break` bypasses the condition check, so `x` may still be non-null.
function whileBreakBypassesCondition(x: string | null, stop: boolean): null {
  while (x !== null) {
    if (stop) {
      break;
    }
    x = null;
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function forBreakBypassesCondition(
  x: string | null,
  stop: boolean,
  next: () => string | null,
): null {
  for (; x !== null; x = next()) {
    if (stop) {
      break;
    }
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Conjunction falsity only guarantees at least one conjunct is false.
function whileAndExitDoesNotNarrowSingleConjunct(
  x: string | null,
  again: boolean,
): null {
  while (x !== null && again) {
    x = null;
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A side-effecting call *inside* the condition after reading a mutable
// captured binding can mutate it before the loop exits.
function whileCondCallMutatesCapturedLocal(init: string | null): null {
  let x: string | null = init;
  const side = (): boolean => {
    x = "mutated";
    return false;
  };
  while (x !== null || side()) {
    x = null;
  }
  // TypeScript also accepts this unsound narrowing.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A side-effecting call *inside* the condition after reading an object field
// can mutate the field before the loop exits.
function whileCondCallMutatesMember(o: { v: string | null }): null {
  const side = (): boolean => {
    o.v = "mutated";
    return false;
  };
  while (o.v !== null || side()) {
    o.v = null;
  }
  // TypeScript also accepts this unsound narrowing.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return o.v;
}

// A write to `x` inside the condition after testing `x` invalidates narrowing.
function whileCondWriteInvalidatesExit(x: string | null, other: string): null {
  while (x !== null || (x = other) === "never") {
    x = null;
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A `for`-init local shadowing an outer variable must not narrow the outer one.
function forInitShadowingDoesNotNarrowOuter(x: string | null): null {
  for (let x: string | null = "inner"; x !== null; x = null) {
    const inner: string = x;
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A break that assigns an uninitialized binding does not make it definitely
// assigned on the normal-exit path.
function whileBreakOnlyInitNotDefinite(
  x: string | null,
  stop: boolean,
): number {
  let y: number;
  while (x !== null) {
    if (stop) {
      y = 1;
      break;
    }
    x = null;
  }
  // @ts-expect-error Variable 'y' is used before being assigned
  return y;
}

// Inside `try/catch`, an exception thrown during the loop body bypasses the
// normal exit, so `catch` must still see the un-narrowed type.
function whileInsideTryCatchDoesNotNarrowCatch(
  x: string | null,
  mayThrow: () => void,
): null {
  try {
    while (x !== null) {
      mayThrow();
      x = null;
    }
  } catch (_e) {
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return null;
}

// Unwritten binding narrowed on break while another binding is written only
// after the break: break path must preserve the widened state, not post-break
// writes (nor claim `y` stayed `"a"`).
function whileBreakPreservesWidenedUnwrittenBinding(
  x: string | null,
  stop: boolean,
  a: "a",
  b: "b",
): "a" {
  let y: "a" | "b" = a;
  while (x !== null) {
    if (stop) {
      break;
    }
    y = b;
    x = null;
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return y;
}
