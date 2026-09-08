/**
 * The null test itself is supported, but the current graph edges cannot yet
 * carry its refinement of value. SKJS accepts this safe program; verification
 * stops at an incoming-edge obligation. This is a verifier limitation, not a
 * producer counterexample. It is the next integration target for null tests.
 */
function nullGuard(value: null | boolean): boolean {
  if (value === null) {
    return false;
  }
  return value;
}
