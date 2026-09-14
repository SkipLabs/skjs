/**
 * Repaired unsoundness witness: seed=true returns false, violating the true
 * result annotation. SKJS now forgets the field refinement across the callback
 * and rejects the return. The fixture retains the runtime counterexample.
 */
function staleCapturedCell(seed: boolean): true {
  const cell: { value: boolean } = { value: seed };
  const reset: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  if (cell.value) {
    const done: null = reset(false);
    return cell.value;
  }
  return true;
}
