// Iteration invokes user code even without an explicit source call. An iterator
// may overwrite cell.value through another alias. Scalar copies stay stable.
function loopEffect(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  for (const value of values) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return cell.value;
  }
  return 0;
}

function spreadEffect(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  const copy = [...values];
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return cell.value;
}

function destructureEffect(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  const [value] = values;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return cell.value;
}

// IteratorClose runs after the body establishes its guard and breaks.
function closeAfterGuard(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  for (const value of values) {
    if (cell.value === null) return 0;
    break;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return cell.value;
}

function consumeNumbers(...values: number[]): void {}
function spreadBeforeArgument(
  cell: { value: number | null },
  values: Iterable<number>,
): void {
  if (cell.value === null) return;
  // @skjs-expect-error Argument is not assignable to the parameter's type
  consumeNumbers(...values, cell.value);
}

function assignedIteration(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  let first: number | undefined;
  [first] = values;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return cell.value;
}

function freshGuardAndSnapshot(
  cell: { value: number | null },
  values: Iterable<number>,
): number {
  if (cell.value === null) return 0;
  const snapshot = cell.value;
  for (const value of values) {
    if (cell.value !== null) return cell.value;
  }
  return snapshot;
}
