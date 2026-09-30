// A key found present by `in` may hold `undefined`: `x?: number` is
// `number | undefined` where the object has the key, and a caller may pass
// `{ x: undefined }`. (TypeScript refuses the body too.)
export function present(o: { x?: number }): number {
  if ("x" in o) return o.x;
  return 0;
}
