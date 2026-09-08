/**
 * SKJS accepts the singleton result, but either Boolean input returns false.
 * The compound loop guard refines the cell read to true. A direct write then
 * stores false, yet SKJS still types the following read as true. No callback
 * or hidden alias is needed. Null skips the body and returns true.
 *
 * The exit-cell union is exported in full and simplifies to a Boolean invariant.
 * Current-content assertions inside the loop are exported separately, but the
 * source graph checker does not yet consume them. The diagnostic regression
 * forgets those assertions; the unchanged singleton claim still fails.
 * Runtime behavior, not an export/contract rejection, establishes the counterexample.
 */
function staleCompound(value: null | boolean): true {
  const cell: { value: boolean } = { value: true };
  while (value !== null && cell.value) {
    cell.value = false;
    return cell.value;
  }
  return true;
}

/**
 * Opposite-polarity regression for the same direct-write defect (#598).
 * The negated guard establishes false, then a true write leaves a stale false
 * read claim. Both Boolean inputs return true against the false annotation;
 * null skips the loop and returns false. SKJS accepts; TypeScript rejects.
 * This is a variant of staleCompound, not an independent bug mechanism.
 */
function staleFlip(value: null | boolean): false {
  const cell: { value: boolean } = { value: false };
  while (value !== null && !cell.value) {
    cell.value = true;
    return cell.value;
  }
  return false;
}
