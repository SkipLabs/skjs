// Object-literal spread distributes over a union-typed source:
// `{ ...(A | B) }` is `(spread A) | (spread B)` (SkipLabs/skjs#714), matching
// TypeScript. Note that a spread still contributes a `[string]: unknown` /
// `[symbol]: unknown` index for the source's possible excess properties (a
// declared type is an open/width-subtype), so a field that must survive a
// spread which lacks it widens — SKJS stays sound where tsc assumes no excess.
type AB = { a: number } | { b: string };

// A field written after the spread is present in every distributed branch and
// keeps its precise type (the spread can't overwrite it).
function fieldAfter(
  x: AB,
): { a: number; k: boolean } | { b: string; k: boolean } {
  return { ...x, k: true };
}

// A branch carrying an index signature distributes like any other.
function indexBranch(
  x: { a: number } | { [k: string]: boolean },
): { a: number } | { [k: string]: boolean } {
  return { ...x };
}

// A branch keyed by a unique symbol distributes too.
declare const sym: unique symbol;
function symbolBranch(
  x: { [sym]: number } | { b: string },
): { [sym]: number } | { b: string } {
  return { ...x };
}

// A local object built from a union spread is multi-branch; assigning a key it
// doesn't already name is an index write against the spread's `[string]`
// excess index (so it type-checks per branch — exercising multi-branch
// local-object support, #745 — rather than internal-erroring).
function localMultiBranch(x: AB): void {
  const o = { ...x };
  o.c = 1;
}

// The cross-product of two union spreads is still rejected against a single
// member (the value could be any of the four branches).
type X = { a: 1 } | { b: 2 };
type Y = { c: 3 } | { d: 4 };
function crossRejects(x: X, y: Y): { a: 1; c: 3 } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x, ...y };
}

// A field written *before* the spread can be overwritten by an excess property
// of the (open) source, so it widens to `unknown` — sound, and stricter than
// TypeScript, which keeps `k: boolean`. Independent of distribution.
function fieldBefore(
  x: AB,
): { k: boolean; a: number } | { k: boolean; b: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { k: true, ...x };
}

// 14 distinct two-branch union spreads would distribute to 2^14 branches,
// exceeding the branch cap: SKJS rejects the literal ("too complex") rather than
// materialize the exponential union (it does not attempt tsc's graceful
// fallback). Converging spreads like `{ ...x, ...x }` are deduplicated and
// stay bounded, so they are unaffected.
function tooManyUnionSpreads(
  p0: { a0: 0 } | { b0: 1 },
  p1: { a1: 0 } | { b1: 1 },
  p2: { a2: 0 } | { b2: 1 },
  p3: { a3: 0 } | { b3: 1 },
  p4: { a4: 0 } | { b4: 1 },
  p5: { a5: 0 } | { b5: 1 },
  p6: { a6: 0 } | { b6: 1 },
  p7: { a7: 0 } | { b7: 1 },
  p8: { a8: 0 } | { b8: 1 },
  p9: { a9: 0 } | { b9: 1 },
  p10: { a10: 0 } | { b10: 1 },
  p11: { a11: 0 } | { b11: 1 },
  p12: { a12: 0 } | { b12: 1 },
  p13: { a13: 0 } | { b13: 1 },
): void {
  // @skjs-expect-error This object literal spreads too many union-typed sources; the distributed union is too complex to represent
  const o = {
    ...p0,
    ...p1,
    ...p2,
    ...p3,
    ...p4,
    ...p5,
    ...p6,
    ...p7,
    ...p8,
    ...p9,
    ...p10,
    ...p11,
    ...p12,
    ...p13,
  };
}
