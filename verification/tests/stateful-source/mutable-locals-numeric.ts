/**
 * Mutable locals holding numbers. Separate from the Boolean forms because a
 * current-content assertion is a finite set of values and a number has none:
 * the wire protocol cannot carry one. Where a claim needs such an assertion
 * the TypeScript producer states nothing and this file does not verify under
 * it, which is its own limit rather than a disagreement about these programs.
 * Under SKJS the storage contract carries them, and they verify.
 */

/**
 * The storage contract is `number`, so the later write meets it and the
 * captured reader observes it. The literal `2` is claimed at the family rather
 * than at its own singleton, which a singleton rule alone cannot type.
 */
function numericCapturedWrite(): number {
  let value: number = 1;
  const read = (): number => value;
  value = 2;
  return read();
}

/**
 * An assignment inside a coalesce: the left arm may short-circuit, so the
 * write happens at most once and the expression still yields what was written
 * rather than the null a bare write would give.
 */
function numericAssignmentInCoalesce(seed: number | undefined): number {
  let state: number | null = null;
  const result: number = seed ?? (state = 1);
  return result;
}
