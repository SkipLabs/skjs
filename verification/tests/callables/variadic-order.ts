// A spread is read where it is written: an actual after it that writes the
// same array does not change what the spread passed.
function readsBeforeLaterWrite(seed: boolean): (boolean | undefined)[] {
  const values: boolean[] = [seed];
  const collect = (...rest: (boolean | undefined)[]): (boolean | undefined)[] =>
    rest;
  return collect(...values, (values[0] = !seed));
}
function effectAfterSpread(seed: boolean): (boolean | undefined)[] {
  const values: boolean[] = [seed];
  const collect = (...rest: (boolean | undefined)[]): (boolean | undefined)[] =>
    rest;
  const id = (x: boolean): boolean => x;
  return collect(...values, id(seed));
}
