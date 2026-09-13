/**
 * Repaired SKJS regression for #598. The compound guard refines the cell read,
 * then a direct write invalidates it. SKJS rejects the singleton return and
 * exports Boolean for the read in its partial first-error snapshot.
 * Either Boolean input returns false; null returns true. The runtime behavior
 * establishes the counterexample independently of verifier proof search.
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
 * Opposite-polarity control for the same repaired defect. Both Boolean inputs
 * return true against the false result annotation; null returns false.
 * SKJS and TypeScript both reject the stale return.
 */
function staleFlip(value: null | boolean): false {
  const cell: { value: boolean } = { value: false };
  while (value !== null && !cell.value) {
    cell.value = true;
    return cell.value;
  }
  return false;
}
