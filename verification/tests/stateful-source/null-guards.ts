/** Eliminate null before returning the same immutable value as a Boolean. */
function nullGuard(value: null | boolean): boolean {
  if (value === null) {
    return false;
  }
  return value;
}

/** Reverse the operands and refine the successful inequality edge. */
function presentGuard(value: null | boolean): boolean {
  if (null !== value) {
    return value;
  }
  return false;
}

/** Negation reverses the guard's successors without losing value identity. */
function negatedGuard(value: null | boolean): boolean {
  if (!(value === null)) {
    return value;
  }
  return false;
}

/** A newer local must not displace the older variable's refinement slot. */
function olderGuard(value: null | boolean): boolean {
  const fallback: boolean = false;
  if (value === null) {
    return fallback;
  }
  return value;
}

/** Refine the loop body, including a break edge, with a supplied head invariant. */
function loopGuard(value: null | boolean): boolean {
  while (value !== null) {
    if (value) {
      break;
    }
    return value;
  }
  return false;
}
