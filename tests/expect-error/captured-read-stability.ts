// FIXME: stale captures below are accepted; only the already-evolved
// inferred binding is rejected. These cases pin the pre-repair behavior.
// A closure may run after its enclosing mutable binding changes.
function staleCapturedLocal(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  if (value !== null) {
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
    const makeRead = () => (): boolean => value;
    value = null;
    return makeRead()();
  }
  return false;
}

// An inferred binding can evolve before its first closure declaration.
function evolvedInferredCapture(): number {
  let value = 1;

  value = "s";
  // @skjs-expect-error Type of the callback's returned value is not assignable to the expected return type
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

  value = "s";
  return read();
}

function staleInferredUnion(seed: boolean | null): boolean {
  let value = seed;
  if (value !== null) {
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
    const read = (): boolean => value;
    reset();
    return read();
  }
  return false;
}
