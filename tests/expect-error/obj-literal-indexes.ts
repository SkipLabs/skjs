// Test: object literal assigned to indexed type
function testObjLiteralToIndexed(): void {
  const a: { [k: string]: number } = { x: 1, y: 2 };
}

// Test: dual assignment to different indexed types (second should fail)
function testDualIndexedAssignment(): void {
  const a = {};
  const b: { [k: string]: number } = a;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const c: { [k: string]: boolean } = a;
}

// Test: local object growth with type annotation should not grow
function testAnnotatedLocalObject(): void {
  let obj: { x: number } = { x: 1 };
  // @skjs-expect-error Property 'y' does not exist on this type
  obj.y = 2;
}

// Test: property access on object literal still errors for missing fields
function testMissingFieldAccess(): void {
  const obj = { x: 10, y: 20 };
  // @skjs-expect-error Property 'z' does not exist on this type
  const z = obj.z;
}

// Test: object literal with mixed types not assignable to single-type index
function testMixedTypesIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: { [k: string]: number } = { x: 1, y: "hello" };
}

// The tests below combine optional fields with index signatures on the super
// type. Note these super types are TS2411-illegal in tsc (a field's type must
// conform to the index value type there); SKJS deliberately uses residual
// index semantics instead — an index covers only the keys not named in the
// type (see skjs-rules.md "Index Signatures") — which makes
// `{ ...; [k: string]: never; [s: symbol]: never }` a closed-object encoding.

// Test: empty literal vs readonly optional field + never indexes.
// Accepted: the literal provably lacks `a` (reads yield undefined, included
// in the optional field type) and a readonly `a?` grants no write
// capability, so nothing conflicts with the never index.
function testEmptyVsReadonlyOptionalNeverIndex(): void {
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

// Test: empty literal vs readonly optional + non-never index (accepted;
// the readonly optional field does not constrain the literal's index).
function testEmptyVsReadonlyOptionalNumberIndex(): void {
  const x: { readonly a?: string; [k: string]: number } = {};
}

// Test: number-index leg routes through the same synthetic string TVar
// (accepted; the number-index check reuses the literal's synthetic string
// index, which the readonly optional field no longer poisons).
function testEmptyVsReadonlyOptionalNumberNeverIndex(): void {
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

// Test: aliasing with READONLY optional view then index view (accepted: a
// readonly `a?` cannot write, so the value is provably still `{}` when g
// reads it).
function testAliasReadonlyOptionalThenIndex(): void {
  const t = {};
  const f: { readonly a?: number } = t;
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

// Test: never-index view then MUTABLE optional view. Rejected: b sealed the
// literal's index to `never`, so c's write grant `number` at "a" is not
// covered (c could write t.a = 5 and a read through b's view would type it
// `never`).
function testAliasNeverIndexThenMutableOptional(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  // @skjs-expect-error Invalid annotation
  const c: { a?: number } = t;
}

// Test: two readonly optional views of the same empty literal (accepted:
// neither view can write, the value stays `{}`).
function testAliasTwoReadonlyOptionals(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  const g: { readonly b?: string } = t;
}

// Test: widened write grant then index view. Rejected: h's mutable
// `a?: number | string` grants writing a string at "a", so i cannot read
// "a" as `number`.
function testAliasWidenedGrantThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  const h: { a?: number | string } = t;
  // @skjs-expect-error Invalid annotation
  const i: { [k: string]: number } = t;
}

declare const sk: unique symbol;

// Test: symbol analogue — readonly optional symbol field + never indexes
// (accepted, same rule as testEmptyVsReadonlyOptionalNeverIndex).
function testEmptyVsReadonlySymbolOptionalNeverIndex(): void {
  const x: {
    readonly [sk]?: number;
    [k: string]: never;
    [s: symbol]: never;
  } = {};
}

// Test: symbol analogue with a MUTABLE optional symbol field. Rejected,
// uniformly with testEmptyVsMutableOptionalNeverIndex: the mutable grant
// `number` is not covered by the `never` index.
function testEmptyVsMutableSymbolOptionalNeverIndex(): void {
  // @skjs-expect-error Invalid annotation
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
