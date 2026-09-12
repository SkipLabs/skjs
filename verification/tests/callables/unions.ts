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

/**
 * Return a closure after guarding its immutable capture. The non-null branch
 * retains both callable alternatives for later invocations; the null branch
 * returns a separate closure that never calls the captured value.
 */
function capturedGuardedCallable(
  f: ((unit: null) => true) | ((unit: null) => false) | null,
): (unit: null) => boolean {
  if (f === null) {
    return (unit: null): boolean => false;
  } else {
    return (unit: null): boolean => f(unit);
  }
}

/**
 * Select an immutable callable alias inside a closure, then capture that alias
 * in another closure. A later call must respect either selected signature;
 * selecting the fallback does not make the original nullable input callable.
 */
function aliasedCallableSelection(
  f: ((unit: null) => true) | null,
  fallback: (unit: null) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean => {
    const selected = f === null ? fallback : f;
    const call: (arg: null) => boolean = (arg: null): boolean => selected(arg);
    return call(unit);
  };
  return invoke(null);
}

/**
 * Both possible callees accept true, although only one accepts false. The
 * selected function can be called at the shared domain, and its result must
 * cover both alternatives.
 */
function sharedCallableDomain(
  choose: boolean,
  wide: (value: boolean) => true,
  narrow: (value: true) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean => {
    const selected = choose ? wide : narrow;
    return selected(true);
  };
  return invoke(null);
}

/**
 * Calls inside the conditional retain the tested Boolean's branch refinement.
 * The true branch can pass it to the true-only callee; the false branch needs
 * the wider Boolean domain. Both singleton call results reach the join.
 */
function branchLocalCallableDomains(
  choose: boolean,
  wide: (value: boolean) => true,
  narrow: (value: true) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    choose ? narrow(choose) : wide(choose);
  return invoke(null);
}
