// A spread copies an optional field present at `undefined`, overwriting the
// field before it: the result's field may be `undefined`. (TypeScript types
// it `string | number`.)
export function optionalOverlap(o: { a?: number }): { a: string | number } {
  return { a: "", ...o };
}
