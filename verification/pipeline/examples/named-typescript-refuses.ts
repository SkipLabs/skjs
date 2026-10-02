// SKJS types an unannotated `[1, "a"]` as a tuple; TypeScript, whose types
// the pipeline follows, as `(number | string)[]`, and refuses the read.
export function first(): number {
  const values = [1, "a"];
  const x: number = values[0];
  return x;
}
