/**
 * The captured-writer witness with its invalidating call replaced by null.
 * The guard and returned cell read are unchanged: no mutation occurs between them.
 */
function stableCapturedCell(seed: boolean): true {
  const cell: { value: boolean } = { value: seed };
  const reset: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  if (cell.value) {
    const done: null = null;
    return cell.value;
  }
  return true;
}

/**
 * The compound-loop witness with its write removed.
 * Verifying the original producer claims requires preserving heap facts through
 * the null test and linking the Boolean guard's result to the current cell.
 */
function stableCompound(value: null | boolean): true {
  const cell: { value: boolean } = { value: true };
  while (value !== null && cell.value) {
    return cell.value;
  }
  return true;
}

/**
 * The same control for the false branch selected by a negated cell read.
 * It must retain the guard-to-cell link through short-circuit evaluation.
 */
function stableFlip(value: null | boolean): false {
  const cell: { value: boolean } = { value: false };
  while (value !== null && !cell.value) {
    return cell.value;
  }
  return false;
}
