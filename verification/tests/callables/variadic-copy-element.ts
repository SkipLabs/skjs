// A spread followed by an actual that runs code is copied where it is
// written. Its dense tuple contract survives the copy, so the Boolean rest
// need not admit undefined just because another argument runs afterwards.
function copiesIntoStrictRest(seed: boolean): boolean[] {
  const pair: [boolean, boolean] = [seed, seed];
  const collect = (...rest: boolean[]): boolean[] => rest;
  return collect(...pair, (pair[0] = !seed));
}
