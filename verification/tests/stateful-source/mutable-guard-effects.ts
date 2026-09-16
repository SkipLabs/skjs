// These controls require reasoning about mutations after a guard. Saved reads
// alone must not let a verifier reuse the pre-mutation value at the return.
function writeAfterGuard(seed: boolean | null): boolean | null {
  let value: boolean | null = seed;
  const read = (): boolean | null => {
    if (value !== null) {
      value = null;
      return value;
    }
    return false;
  };
  return read();
}

function callAfterGuard(seed: boolean | null): boolean | null {
  let value: boolean | null = seed;
  const reset = (): null => {
    value = null;
    return null;
  };
  const read = (): boolean | null => {
    if (value !== null) {
      reset();
      return value;
    }
    return false;
  };
  return read();
}
