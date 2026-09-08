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

/** A null guard exposes the existing stable cell contract before a read. */
function nullableCellRead(value: boolean): boolean {
  const cell: null | { value: boolean } = { value: value };
  if (cell === null) {
    return false;
  }
  return cell.value;
}

/** Refining the reference permits a write, without narrowing its contents. */
function nullableCellWrite(value: boolean): boolean {
  const cell: null | { value: boolean } = { value: value };
  if (cell !== null) {
    cell.value = true;
    return cell.value;
  }
  return false;
}

/** A callback can guard a captured nullable reference and safely read it. */
function capturedNullableCell(value: boolean): boolean {
  const cell: null | { value: boolean } = { value: value };
  const read: (unit: null) => boolean = (unit: null): boolean => {
    if (cell === null) {
      return false;
    } else {
      return cell.value;
    }
  };
  return read(null);
}

/** A null guard exposes an already-supported unary primitive call contract. */
function optionalCallback(value: boolean): boolean {
  const callback: null | ((x: boolean) => boolean) = (x: boolean): boolean =>
    !x;
  if (callback === null) {
    return false;
  }
  return callback(value);
}

/** Both null and a locally allocated cell satisfy the declared union result. */
function maybeCell(present: boolean): null | { value: boolean } {
  if (present) {
    const cell: { value: boolean } = { value: present };
    return cell;
  }
  return null;
}

/** An optional function result comes from a locally checked closure or null. */
function maybeCallback(present: boolean): null | ((x: boolean) => boolean) {
  if (present) {
    const callback: (x: boolean) => boolean = (x: boolean): boolean => !x;
    return callback;
  }
  return null;
}

/** A ternary refines its nullable input in the selected expression arm. */
function ternaryGuard(value: null | boolean): boolean {
  return value === null ? false : value;
}

/** Allocate only on the present path, then guard the resulting local union. */
function chosenCell(present: boolean, value: boolean): boolean {
  const cell: null | { value: boolean } = present ? { value: value } : null;
  return cell === null ? false : cell.value;
}

/** Choose a checked callback dynamically; the null arm never calls it. */
function chosenCallback(present: boolean, value: boolean): boolean {
  const callback: null | ((x: boolean) => boolean) = present
    ? (x: boolean): boolean => !x
    : null;
  return callback === null ? false : callback(value);
}

/** Evaluate an effectful condition once and only execute its selected arm. */
function ternaryEffects(value: boolean): boolean {
  const cell: { value: boolean } = { value: false };
  const result: boolean = (cell.value = value)
    ? (cell.value = false)
    : (cell.value = true);
  return cell.value;
}

/** The same ternary proof construction works inside a captured closure. */
function capturedTernary(value: null | boolean): boolean {
  const choose: (unit: null) => boolean = (unit: null): boolean =>
    value !== null ? value : false;
  return choose(null);
}

/** Null selects the fallback; false is already a value and must survive. */
function coalesceBoolean(value: null | boolean): boolean {
  return value ?? true;
}

/** A fallback allocation turns an optional local cell into a usable cell. */
function coalesceCell(present: boolean, value: boolean): boolean {
  const optional: null | { value: boolean } = present ? { value: value } : null;
  const fallback: { value: boolean } = { value: false };
  const cell: { value: boolean } = optional ?? fallback;
  return cell.value;
}

/** Select one of two checked closures without an external callback assumption. */
function coalesceCallback(present: boolean, value: boolean): boolean {
  const optional: null | ((x: boolean) => boolean) = present
    ? (x: boolean): boolean => !x
    : null;
  const fallback: (x: boolean) => boolean = (x: boolean): boolean => x;
  const callback: (x: boolean) => boolean = optional ?? fallback;
  return callback(value);
}

/** The fallback write runs only for null, including when the left value is false. */
function coalesceWrite(value: null | boolean): boolean {
  const cell: { value: boolean } = { value: false };
  const result: boolean = value ?? (cell.value = true);
  return cell.value;
}

/** A call on the left toggles a cell: repeating it would change the result. */
function coalesceOnce(value: boolean): boolean {
  const cell: { value: boolean } = { value: value };
  const left: (unit: null) => null = (unit: null): null => {
    cell.value = !cell.value;
    return null;
  };
  return left(null) ?? cell.value;
}

/** In the fallback the immutable input is known to be null, even in a closure. */
function coalesceAlias(value: null | boolean): null | boolean {
  const choose: (unit: null) => null | boolean = (unit: null): null | boolean =>
    value ?? value;
  return choose(null);
}

/** Nested coalescing preserves both operand scopes and short-circuit choices. */
function coalesceNested(left: null | boolean, right: null | boolean): boolean {
  return left ?? right ?? false;
}
