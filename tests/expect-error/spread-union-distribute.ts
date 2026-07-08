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
// exceeding the branch cap. Rather than reject the literal, SKJS soundly
// degrades the overflowing spread to an open over-approximation and warns; the
// literal still type-checks (TypeScript accepts it too — its limit is ~100k).
// Converging spreads like `{ ...x, ...x }` are deduplicated and stay bounded,
// so they never reach the cap.
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
    // @skjs-expect-warning This object spread distributes over more than 10000 union branches; its type is over-approximated to an open object, so some properties are typed 'unknown'
    ...p13,
  };
  // The literal degrades (non-fatal) instead of aborting the definition, so
  // this unrelated error now surfaces.
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const s: string = 42;
}

// An over-cap spread whose OVERFLOWING source shares a field across its
// branches: `c` is present in both branches of `pl`. Under distribution `o.c`
// is `number` (as in TypeScript). This literal overflows the branch cap on the
// final `...pl` spread, so that spread degrades to an open object: `c` is
// dropped and `o.c` becomes `unknown` — sound, but less precise than tsc here.
function capDegradeDropsCommonSourceField(
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
  pl: { c: number; d: 0 } | { c: number; e: 1 },
): void {
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
    // @skjs-expect-warning This object spread distributes over more than 10000 union branches; its type is over-approximated to an open object, so some properties are typed 'unknown'
    ...pl,
  };
  // PRECISION (SkipLabs/skjs#747 follow-up): once the cap degrades `...pl` to an
  // open object, `c` is dropped and `o.c` is `unknown`, so `cc` errors — a more
  // precise collapse that kept fields common to all of `pl`'s branches would
  // keep `c: number` here (TypeScript does; skjs is soundly stricter). Reading
  // `o.c` as `unknown` stays sound.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const cc: number = o.c;
  const uc: unknown = o.c;
}

// A field written after a union spread gets its own growable type variable in
// every distributed branch, so a union target whose members want different
// widths for that field (k: boolean vs k: true) checks each branch
// independently — as in TypeScript.
type Correlated = { a: number; k: boolean } | { b: string; k: true };
function sharedTvarCorrelatedTarget(x: AB): Correlated {
  return { ...x, k: true };
}

// The SAME union written INLINE in the annotation (not behind the `Correlated`
// alias above) is likewise checked member by member: the literal matches the
// `k: true` member, so its `k` stays `'true'` instead of being widened to
// `boolean` by the other member. TypeScript accepts both forms.
function inlineUnionTarget():
  | { a: number; k: boolean }
  | { b: string; k: true } {
  return { b: "s", k: true };
}

// A nested growable type variable (the empty array) is still seeded from the
// matching member, so `b` commits to `number[]`.
function nestedSeedInlineUnion():
  | { a: number[]; k: boolean }
  | { b: number[]; k: true } {
  return { b: [], k: true };
}

// Soundness: a literal matching no member is rejected — `{ c, k }` has neither
// the first member's `a` nor the second member's `b`.
function inlineUnionNoMemberMatches():
  | { a: number; k: boolean }
  | { b: string; k: true } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { c: 0, k: true };
}

// Discriminating a spread result with `in` no longer recovers the field's
// type: in the branch that lacks `a`, the key is covered only by the spread's
// `[string]: unknown` excess index, so `o.a` is `unknown` (sound — the source
// may carry an excess `a` of any type at runtime; the old collapse's
// `a?: number` accepted an unsound read here). TypeScript accepts.
function inNarrowAfterSpread(x: AB): number {
  const o = { ...x };
  if ("a" in o) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return o.a;
  }
  return 0;
}
