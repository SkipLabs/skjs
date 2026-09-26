// TypeScript types the written `k` per arm of the expected union: `boolean`
// where the copy has `a`, `true` where it has `b`. The copy's field is
// allocated at one type for both, and a writable field is invariant.
type AB = { a: number } | { b: string };
type Tagged = { a: number; k: boolean } | { b: string; k: true };

export function tag(x: AB): Tagged {
  return { ...x, k: true };
}
