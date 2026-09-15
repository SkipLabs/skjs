/**
 * A recorded boundary: a guard on a mutable local, inside the closure that
 * reads it. The read yields the storage contract and the guard does not refine
 * it. Only an immutable slot's saved value may be substituted for a tested
 * one, because a write through the cell between the test and the read would
 * invalidate it.
 *
 * SKJS accepts this and it is true at runtime, so this is a limit of what the
 * pipeline establishes, not a finding about the program. Establishing it needs
 * an observation on the read and its invalidation across writes, calls and
 * back edges — which is also what the loop-carried target waits on. It has its
 * own file so that it does not carry its siblings' verdicts down with it.
 */
function guardedMutableRead(): boolean {
  let value: boolean | null = null;
  value = true;
  const read = (): boolean => {
    if (value !== null) {
      return value;
    }
    return false;
  };
  value = null;
  return read();
}
