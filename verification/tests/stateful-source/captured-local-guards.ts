// The guard is evaluated when the closure is called. Its saved read is valid
// only along branches that cannot mutate the captured location.
function guardedCapturedRead(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  const read = (): boolean => {
    if (value !== null) {
      return value;
    }
    return false;
  };
  value = null;
  return read();
}
