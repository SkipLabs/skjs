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

/** A callback narrows its own nullable parameter before returning it. */
function callbackGuard(value: null | boolean): boolean {
  const choose: (x: null | boolean) => boolean = (
    x: null | boolean,
  ): boolean => {
    if (x === null) {
      return false;
    } else {
      return x;
    }
  };
  return choose(value);
}

/** A closure can narrow a captured immutable value without narrowing a cell. */
function capturedGuard(value: null | boolean): boolean {
  const choose: (unit: null) => boolean = (unit: null): boolean => {
    if (null !== value) {
      return value;
    } else {
      return false;
    }
  };
  return choose(null);
}

/** A negated guard preserves effects in its selected callback arm. */
function effectfulCallbackGuard(value: null | boolean): boolean {
  const cell: { value: boolean } = { value: false };
  const choose: (x: null | boolean) => boolean = (
    x: null | boolean,
  ): boolean => {
    if (!(x === null)) {
      cell.value = x;
      return x;
    } else {
      return false;
    }
  };
  const result: boolean = choose(value);
  return cell.value;
}
