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
