// SKJS accepts this stale captured-cell refinement; seed=true returns false.
// The original export hits the unequal read/write contract boundary. The test
// also weakens those reference refinements and checks the stale read obligation.
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
