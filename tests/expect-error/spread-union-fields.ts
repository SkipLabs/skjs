// Object-literal spread of a union-typed source distributes over the union:
// `{ ...(A | B) }` is `(spread A) | (spread B)` (SkipLabs/skjs#714), matching
// TypeScript.
type AB = { a: number } | { b: string };

// Distribution yields `{ a: number } | { b: string }` = `AB`, so this is now
// accepted (it was rejected while spread collapsed the union into one open
// object).
function spreadUnion(x: AB): AB {
  return { ...x };
}

// Into a Partial-style target, distribution is stricter than TypeScript and
// stricter than the former collapse. In the `{ a: number }` branch, `b` is not
// a field — it is only covered by the `[string]: unknown` index the spread adds
// for the source's possible excess properties — so `b` is `unknown`, not
// assignable to `b?: string`. Sound (a value of `AB` may carry an excess `b` of
// any type); TypeScript assumes no excess and accepts it.
function spreadIntoPartial(x: AB): { a?: number; b?: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}
