// A spread followed by an actual that runs code is copied where it is
// written, and the copy is typed as an array of any length. Spreading it into
// a rest whose element type does not admit `undefined` is refused, although
// the tuple copied here has no hole.
function copiesIntoStrictRest(seed: boolean): boolean[] {
  const pair: [boolean, boolean] = [seed, seed];
  const collect = (...rest: boolean[]): boolean[] => rest;
  const id = (x: boolean): boolean => x;
  return collect(...pair, id(seed));
}
