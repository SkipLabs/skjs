// The default is universally valid, but its input contract needs T | undefined
// in the rigid claim/certificate language; replacing T with its bound is wrong.
function rigidDefault(seed: boolean): boolean {
  const pick = <T>(value: T, copy: T = value): T => copy;
  return pick(seed);
}
