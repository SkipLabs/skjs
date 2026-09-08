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
 * This semantic proof is not yet a source-checker certificate. Editing the
 * read claim to true still fails current proof search; graph typing and the
 * certificate checker do not yet consume the heap-observation rules.
 */
function writeRefinedRead(): true {
  const cell: { value: boolean } = { value: false };
  cell.value = true;
  return cell.value;
}
