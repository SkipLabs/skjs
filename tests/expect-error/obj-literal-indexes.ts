// Test: object literal assigned to indexed type
function testObjLiteralToIndexed(): void {
  const a: { [k: string]: number } = { x: 1, y: 2 };
}

// Test: dual assignment to different indexed types (second should fail)
function testDualIndexedAssignment(): void {
  const a = {};
  const b: { [k: string]: number } = a;
  // @skjs-expect-error Invalid annotation
  const c: { [k: string]: boolean } = a;
}

// Test: local object growth with type annotation should not grow
function testAnnotatedLocalObject(): void {
  let obj: { x: number } = { x: 1 };
  // @skjs-expect-error Unbound field: y
  obj.y = 2;
}

// Test: property access on object literal still errors for missing fields
function testMissingFieldAccess(): void {
  const obj = { x: 10, y: 20 };
  // @skjs-expect-error Unbound field: z
  const z = obj.z;
}

// Test: object literal with mixed types not assignable to single-type index
function testMixedTypesIndex(): void {
  // @skjs-expect-error Invalid annotation
  const a: { [k: string]: number } = { x: 1, y: "hello" };
}

// The tests below combine optional fields with index signatures on the super
// type. Note these super types are TS2411-illegal in tsc (a field's type must
// conform to the index value type there); SKJS deliberately uses residual
// index semantics instead — an index covers only the keys not named in the
// type (see skjs-rules.md "Index Signatures") — which makes
// `{ ...; [k: string]: never; [s: symbol]: never }` a closed-object encoding.

// Test: empty literal vs readonly optional field + never indexes
// FIXME: should be accepted — the literal provably lacks `a`, and readonly
// `a?` grants no write capability; rejection comes from the optional-field
// leg poisoning the literal's synthetic index TVar with `number` before the
// never-index check runs.
function testEmptyVsReadonlyOptionalNeverIndex(): void {
  // @skjs-expect-error Invalid annotation
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Test: literal providing the optional field vs never indexes (accepted)
function testProvidedOptionalNeverIndex(): void {
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {
    a: 1,
  };
}

// Test: excess property vs never index (rejected: `2` is not `never`)
function testExcessVsNeverIndex(): void {
  // @skjs-expect-error Invalid annotation
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {
    a: 1,
    b: 2,
  };
}

// Test: MUTABLE optional field + never index. Rejected: a mutable `a?`
// grants write capability at key "a", which the never index cannot absorb.
function testEmptyVsMutableOptionalNeverIndex(): void {
  // @skjs-expect-error Invalid annotation
  const x: { a?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Test: empty literal vs readonly optional + non-never index
// FIXME: should be accepted — same poisoning as
// testEmptyVsReadonlyOptionalNeverIndex, with a `number` index instead of
// `never` (the optional leg locks the TVar to `string` first).
function testEmptyVsReadonlyOptionalNumberIndex(): void {
  // @skjs-expect-error Invalid annotation
  const x: { readonly a?: string; [k: string]: number } = {};
}

// Test: number-index leg routes through the same synthetic string TVar
// FIXME: should be accepted — same poisoning as
// testEmptyVsReadonlyOptionalNeverIndex; the number-index check reuses the
// literal's synthetic string index, so it fails the same way.
function testEmptyVsReadonlyOptionalNumberNeverIndex(): void {
  // @skjs-expect-error Invalid annotation
  const x: {
    readonly a?: number;
    [k: string]: never;
    [n: number]: never;
    [s: symbol]: never;
  } = {};
}

// Test: aliasing defense — a MUTABLE optional view grants write capability,
// so a later incompatible index view must be rejected (f may write number at
// "a"; g would read it as boolean).
function testAliasMutableOptionalThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  // @skjs-expect-error Invalid annotation
  const g: { [k: string]: boolean } = t;
}

// Test: aliasing with READONLY optional view then index view
// FIXME: should be accepted — a readonly `a?` cannot write, so the value is
// provably still `{}` when g reads it; today the read type poisons the TVar.
function testAliasReadonlyOptionalThenIndex(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // @skjs-expect-error Invalid annotation
  const g: { [k: string]: boolean } = t;
}

// Test: aliasing defense — mutable grant then conflicting optional view
// (f may write number at "a"; g would read it as string | undefined).
function testAliasMutableOptionalThenOptional(): void {
  const t = {};
  const f: { a?: number } = t;
  // @skjs-expect-error Invalid annotation
  const g: { b?: string } = t;
}

// Test: never-index view then MUTABLE optional view
// FIXME: UNSOUND acceptance — b sealed the literal's index to `never`, then
// c grants write capability `number` at "a"; c can write t.a = 5 and a read
// through b's view types it `never`. The second assignment must be rejected.
function testAliasNeverIndexThenMutableOptional(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  const c: { a?: number } = t;
}

// Test: two readonly optional views of the same empty literal
// FIXME: should be accepted — neither view can write, the value stays `{}`.
function testAliasTwoReadonlyOptionals(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // @skjs-expect-error Invalid annotation
  const g: { readonly b?: string } = t;
}

// Test: widened write grant then index view
// FIXME: UNSOUND acceptance — h's mutable `a?: number | string` grants
// writing a string at "a", but only the setter side records it; i then reads
// "a" as `number`. The third assignment must be rejected.
function testAliasWidenedGrantThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  const h: { a?: number | string } = t;
  const i: { [k: string]: number } = t;
}

declare const sk: unique symbol;

// Test: symbol analogue — readonly optional symbol field + never indexes.
// Accepted today: the symbol-fields leg runs after the symbol-index check,
// so the synthetic symbol TVar is already sealed to `never` (bottom) and the
// readonly optional read check passes. Pins the working ordering.
function testEmptyVsReadonlySymbolOptionalNeverIndex(): void {
  const x: {
    readonly [sk]?: number;
    [k: string]: never;
    [s: symbol]: never;
  } = {};
}

// Test: symbol analogue with a MUTABLE optional symbol field
// FIXME: accepted today only because of the string/symbol ordering
// asymmetry (the symbol-index leg runs before the symbol-fields leg). For
// uniformity with testEmptyVsMutableOptionalNeverIndex and for the aliasing
// defense, the mutable grant `number` must be rejected against the sealed
// `never` index.
function testEmptyVsMutableSymbolOptionalNeverIndex(): void {
  const x: { [sk]?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Test: symbol aliasing defense — mutable symbol grant then symbol-index
// view (f may write number at [sk]; g would read it as string).
function testAliasMutableSymbolOptionalThenIndex(): void {
  const t = {};
  const f: { [sk]?: number } = t;
  // @skjs-expect-error Invalid annotation
  const g: { [s: symbol]: string } = t;
}
