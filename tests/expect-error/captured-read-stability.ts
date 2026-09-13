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

// An inferred alias created after narrowing retains the source object
// contract, so its callback cannot promise a transient non-null field.
function inferredAliasCapture(cell: { value: boolean | null }): boolean {
  if (cell.value !== null) {
    const alias = cell;
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => alias.value;
    cell.value = null;
    return read();
  }
  return false;
}

// The initializer participates in the captured inference contract, so the
// unguarded numeric read rejects null. tsc rejects implicit any here.
function evolvingNullCapture(): number {
  let value = null;
  value = 1;
  // @skjs-expect-error Type of the callback's returned value is not assignable to the expected return type
  const read = (): number => value;
  value = "s";
  return read();
}

// A fresh check narrows the inferred field within this invocation, while the
// const object's contents contract still admits later null writes.
function checkedInferredObject(seed: boolean | null): boolean {
  const cell = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) {
      return cell.value;
    }
    return false;
  };
  cell.value = null;
  return read();
}

// A null check at invocation time should handle both initializer and later
// numeric writes. tsc requires an annotation here (implicit any).
function checkedEvolvingCapture(): number {
  let value = null;
  value = 1;
  const read = (): number => {
    if (value !== null) return value;
    return 0;
  };
  value = null;
  return read();
}
// Once the read seals the numeric-or-undefined contract, a string write
// cannot invalidate it. tsc rejects implicit any instead.
function sealedEvolvingCapture(): number {
  let value = undefined;
  value = 1;
  const read = (): number => {
    if (value !== undefined) return value;
    return 0;
  };
  // @skjs-expect-error Type is not assignable to the variable's type
  value = "s";
  return read();
}

// Narrowing after alias creation must not replace the inherited contract
// used by a captured read.
function aliasThenNarrow(cell: { value: boolean | null }): boolean {
  const alias = cell;
  if (alias.value !== null) {
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    const read = (): boolean => alias.value;
    cell.value = null;
    return read();
  }
  return false;
}
// Transferring a contract through several aliases must preserve fresh checks.
function checkedAliasChain(cell: { value: boolean | null }): boolean {
  const first = cell;
  const alias = first;
  const read = (): boolean => {
    if (alias.value !== null) return alias.value;
    return false;
  };
  cell.value = null;
  return read();
}
// Replacing a mutable alias must preserve its inherited object contract.
function reassignedAlias(cell: { value: boolean | null }): boolean {
  let alias = cell;
  const read = (): boolean | null => alias.value;
  // @ts-expect-error Type is not assignable to the variable's type
  alias = { value: "s" };
  return read() === true;
}

// FIXME: replacing the object after the callback is checked changes its
// numeric result to a string. tsc rejects the replacement.
function replacedObjectCapture(): number {
  let cell = { value: 1 };
  const read = (): number => cell.value;
  cell = { value: "changed" };
  return read();
}

// A guarded callback can handle a compatible whole-object replacement.
function checkedMutableObjectReplacement(seed: boolean | null): boolean {
  let cell = { value: seed };
  const read = (): boolean => {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    if (cell.value !== null) return cell.value;
    return false;
  };
  cell = { value: null };
  return read();
}

// FIXME: the first read occurs in a nested callback/branch. Its contract must
// survive that scope before a later replacement drops the required field.
function branchObjectCapture(flag: boolean): number {
  let cell = { value: 1 };
  let read: () => number = (): number => 0;
  if (flag) read = (): number => cell.value;
  cell = { other: true };
  return read();
}
