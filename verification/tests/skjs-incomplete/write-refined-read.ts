/**
 * Producer precision gap: this always returns true, but SKJS types the final
 * read as boolean and rejects the declared true result; TypeScript accepts it.
 * The write establishes the exact current contents, independently of the
 * persistent Boolean storage invariant. The original return-entry claim forgets
 * that and does not verify; supplying { value: boolean = true } there repairs
 * it. WriteRefinedRead.lean proves the body and its execution, and
 * tests/write-observations.js pins the source shape.
 */
function writeRefinedRead(): true {
  const cell: { value: boolean } = { value: false };
  cell.value = true;
  return cell.value;
}
