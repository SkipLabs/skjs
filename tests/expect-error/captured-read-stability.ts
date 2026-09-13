// A closure may run after its enclosing mutable binding changes.
function staleCapturedLocal(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => value;
    value = null;
    return read();
  }
  return false;
}

// Checking at invocation time establishes a fresh narrowing in the closure.
function checkedCapturedLocal(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  const read = (): boolean => {
    if (value !== null) {
      return value;
    }
    return false;
  };
  value = null;
  return read();
}

// Copying the value into a const gives the closure a stable snapshot.
function snapshotCapturedLocal(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  if (value !== null) {
    const snapshot = value;
    const read = (): boolean => snapshot;
    value = null;
    return read();
  }
  return false;
}

// Parameters are mutable bindings too, including through nested closures.
function staleCapturedParameter(value: boolean | null): boolean {
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const makeRead = () => (): boolean => value;
    value = null;
    return makeRead()();
  }
  return false;
}

// Captured concrete primitive bindings keep their initializer's type as
// a write contract, including writes before the first closure declaration.
function evolvedInferredCapture(): number {
  let value = 1;
  // @ts-expect-error Type is not assignable to the variable's type
  value = "s";
  const read = (): number => value;
  return read();
}

// Without a capture of the mutable binding, SKJS still permits evolution
// (tsc rejects the string assignment). Copying the value makes a stable capture.
function evolvedInferredSnapshotStillString(): string {
  let value = 1;
  value = "s";
  const snapshot = value;
  const read = (): string => snapshot;
  return read();
}

// The mutable parameter's declared contract also removes stale field facts.
function staleCapturedField(cell: { value: boolean | null }): boolean {
  if (cell.value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => cell.value;
    cell.value = null;
    return read();
  }
  return false;
}

// A parameter with no writes keeps its value narrowing across capture.
function neverReassigned(value: boolean | null): boolean {
  if (value !== null) {
    const read = (): boolean => value;
    return read();
  }
  return false;
}

// The summary must include writes in a nested function's default initializer.
function writtenByDefault(value: boolean | null): boolean {
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => value;
    const reset = (ignored: boolean | null = (value = null)): null => null;
    const resetResult = reset();
    return read();
  }
  return false;
}

// A stable reference does not stabilize fields that another alias may change.
function stableReferenceMutableContents(
  cell: { value: boolean | null },
  reset: () => void,
): boolean {
  if (cell.value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => cell.value;
    reset();
    return read();
  }
  return false;
}

// Destructuring defaults execute code; absence of a simple assignment target
// must not be mistaken for absence of writes.
function writtenByDestructuring(
  value: boolean | null,
  source: { reset?: boolean | null },
): boolean {
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => value;
    const { reset = (value = null) } = source;
    return read();
  }
  return false;
}

// A const binding fixes the reference, not the contents of the object.
function staleAnnotatedConstField(seed: boolean | null): boolean {
  const cell: { value: boolean | null } = { value: seed };
  if (cell.value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => cell.value;
    cell.value = null;
    return read();
  }
  return false;
}

function checkedAnnotatedConstField(seed: boolean | null): boolean {
  const cell: { value: boolean | null } = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) {
      return cell.value;
    }
    return false;
  };
  cell.value = null;
  return read();
}

// In contrast, the narrowed value of a const primitive cannot be overwritten.
function stableAnnotatedConstValue(seed: boolean | null): boolean {
  const value: boolean | null = seed;
  if (value !== null) {
    const read = (): boolean => value;
    return read();
  }
  return false;
}

// A later same-frame assignment currently invalidates an inferred capture.
function staleInferredPrimitive(): number {
  let value = 1;
  const read = (): number => value;
  // @ts-expect-error Type is not assignable to the variable's type
  value = "s";
  return read();
}

function staleInferredUnion(seed: boolean | null): boolean {
  let value = seed;
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => value;
    value = null;
    return read();
  }
  return false;
}

function inferredPrimitiveCompatibleWrite(): number {
  let value = 1;
  const read = (): number => value;
  value = 2;
  return read();
}

// A setter checked earlier may run after the reader is created. Its writes
// must not escape the contract just because it precedes the reader in source.
function inferredSetterBeforeReader(seed: boolean | null): boolean {
  let value = seed;
  const reset = (): void => {
    value = null;
  };
  if (value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => value;
    reset();
    return read();
  }
  return false;
}

// A fresh inferred object's field already keeps the nullable member in its
// read type. This stale read is rejected without an explicit object annotation.
function inferredObjectCapture(seed: boolean | null): boolean {
  const cell = { value: seed };
  if (cell.value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => cell.value;
    cell.value = null;
    return read();
  }
  return false;
}

// FIXME: an inferred alias created after narrowing exports the transient read
// fact. SKJS accepts the stale callback; tsc rejects its nullable result.
function inferredAliasCapture(cell: { value: boolean | null }): boolean {
  if (cell.value !== null) {
    const alias = cell;
    const read = (): boolean => alias.value;
    cell.value = null;
    return read();
  }
  return false;
}

// FIXME: the unresolved initializer bypasses the primitive capture contract;
// a later write changes the value returned as number. tsc rejects implicit any.
function evolvingNullCapture(): number {
  let value = null;
  value = 1;
  const read = (): number => value;
  value = "s";
  return read();
}

// FIXME: invocation-time checking is safe, but inference still prevents the
// field narrowing from reaching this read. tsc accepts this function.
function checkedInferredObject(seed: boolean | null): boolean {
  const cell = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) {
      // @skjs-expect-error Type of returned value is not assignable to the function's return type
      return cell.value;
    }
    return false;
  };
  cell.value = null;
  return read();
}
