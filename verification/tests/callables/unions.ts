// A closure's null guard must retain both possible callable results.
function guardedCallableUnion(
  f: ((unit: null) => true) | ((unit: null) => false) | null,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f === null ? false : f(unit);
  return invoke(null);
}

/**
 * The right side of && runs only when the captured value is callable. The
 * call returns true, but skipping it produces false.
 */
function andGuardedCallable(f: ((unit: null) => true) | null): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f !== null && f(unit);
  return invoke(null);
}

/**
 * The right side of || runs only after the null test fails. A null input
 * returns true without invoking anything.
 */
function orGuardedCallable(f: ((unit: null) => false) | null): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f === null || f(unit);
  return invoke(null);
}

// Coalescing selects a function before invocation; either signature can supply
// the result, and both null and undefined must select the fallback.
function coalescedCallable(
  f: ((unit: null) => true) | null | undefined,
  fallback: (unit: null) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    (f ?? fallback)(unit);
  return invoke(null);
}
