/**
 * A remaining observation-transfer boundary: this program needs the precise
 * contents established before closure creation at the next statement entry.
 * The guarded closure body itself is supported, as captured-local-guards.ts
 * demonstrates with a broader incoming value. Keep this case unchanged as a
 * record of the separate precision limitation.
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
