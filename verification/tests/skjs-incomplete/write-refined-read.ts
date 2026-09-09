/**
 * Producer precision gap: this function always returns true, but SKJS types
 * the final read as boolean and rejects the declared true result. TypeScript
 * accepts it. The write establishes the exact current contents, independently
 * of the persistent Boolean storage invariant.
 *
 * WriteRefinedRead.lean proves the complete allocate/write/read body using
 * the heap-observation rules, for every admissible initial heap, and proves
 * its five-step execution. No ownership or non-escape premise is needed for
 * the general write-then-read rule: no operation intervenes that could mutate
 * the cell. The source shape is pinned by tests/write-observations.js.
 *
 * The original broad return-entry claim does not verify locally: it forgets
 * the write's current-true fact. Supplying { value: boolean = true } at that
 * entry repairs the proof, even with the Boolean read claim. The incoming
 * write edge must establish the observation. False observations are rejected.
 */
function writeRefinedRead(): true {
  const cell: { value: boolean } = { value: false };
  cell.value = true;
  return cell.value;
}
