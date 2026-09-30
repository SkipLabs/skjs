// An optional field given `undefined`: the pipeline reads `x?: number`
// exactly, as absent or a number, where TypeScript's default reading also
// admits a present `undefined`.
type Opt = { x?: number };
export function make(): Opt {
  const o: Opt = { x: undefined };
  return o;
}
