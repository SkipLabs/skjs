// An optional field given `undefined`: `x?: number` is `number | undefined`
// where the object has the key, so a literal may write `undefined` there, and
// a spread copies the key as it is.
type Opt = { x?: number };
export function make(): Opt {
  const o: Opt = { x: undefined };
  return o;
}
export function copy(o: Opt): { x?: number } {
  return { ...o };
}
