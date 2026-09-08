/**
 * Unsoundness witness: SKJS accepts the true result annotation, but seed=true
 * returns false. The callback invalidates the tested cell contents before the
 * return reads them again. The original export hits the unequal
 * read/write-contract gate; a candidate forgetting that reference refinement
 * is rejected at the stale read. See this directory’s README for the
 * distinction.
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
