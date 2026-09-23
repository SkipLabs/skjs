// TypeScript accepts this, but the write leaves a hole at index 1. Spreading
// materializes it as undefined in the returned array, violating boolean[].
function spreadsArrayIntoRest(seed: boolean): boolean[] {
  const values: boolean[] = [seed];
  values[2] = seed;
  const collect = (...rest: boolean[]): boolean[] => rest;
  return collect(...values);
}
