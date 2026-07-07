// Object-literal spread of a union-typed source. SKJS currently collapses the
// branches into one open object (a sound over-approximation), so returning the
// result against a distributed target is rejected. TypeScript distributes the
// spread — `{ ...(A | B) }` is `(spread A) | (spread B)` — and these pins encode
// today's collapse behavior; distribution (SkipLabs/skjs#714) flips them.
type AB = { a: number } | { b: string };

// A field written before the spread is present in every distributed branch.
function fieldBefore(
  x: AB,
): { k: boolean; a: number } | { k: boolean; b: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { k: true, ...x };
}

// A field written after the spread is likewise present in every branch.
function fieldAfter(
  x: AB,
): { a: number; k: boolean } | { b: string; k: boolean } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x, k: true };
}

// Two union spreads cross-product: `{a}|{b}` × `{c}|{d}` is four branches, which
// is exactly `X & Y` (distributed intersection).
type X = { a: 1 } | { b: 2 };
type Y = { c: 3 } | { d: 4 };
function crossProduct(x: X, y: Y): X & Y {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x, ...y };
}

// The cross-product is still rejected against a single member (the value could
// be any of the four branches) — this stays an error under distribution too.
function crossRejects(x: X, y: Y): { a: 1; c: 3 } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x, ...y };
}

// A branch carrying an index signature distributes like any other.
function indexBranch(
  x: { a: number } | { [k: string]: boolean },
): { a: number } | { [k: string]: boolean } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}

// A branch keyed by a unique symbol distributes too.
declare const sym: unique symbol;
function symbolBranch(
  x: { [sym]: number } | { b: string },
): { [sym]: number } | { b: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}

// A local object built from a union spread is multi-branch, and grows per branch
// (exercises the multi-branch local-object support from #745). TypeScript has no
// growth model, so it rejects `o.c = 1` where SKJS soundly adds the field.
function localAfterSpread(
  x: AB,
): { a: number; c: number } | { b: string; c: number } {
  const o = { ...x };
  // TypeScript rejects this (no growth model); SKJS soundly grows the fresh
  // local object, adding `c` to each branch.
  o.c = 1;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return o;
}
