/**
 * SKJS rejects this safe return: reaching it means value is not null.
 * The null input loops forever; the verifier proves type safety, not termination.
 * Normal partial claims can be repaired at the final entry and returned expression.
 */
function exitGuard(value: null | boolean): boolean {
  while (value === null) {
    continue;
  }
  return value;
}
