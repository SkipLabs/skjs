/**
 * Unsoundness witness: SKJS accepts the true result annotation, but seed=true
 * returns false. The callback invalidates the tested cell contents before the
 * return reads them again. The original exported current-content assertion
 * now fails a checked incoming-edge obligation after the callback. A candidate
 * forgetting that reference observation still fails at the stale read.
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
