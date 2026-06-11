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

// ============================================================================
// Optional fields + index signatures on the super type (closed-object
// encoding `{ ...; [k: string]: never; [s: symbol]: never }`). These super
// types are TS2411-illegal in tsc; SKJS uses residual index semantics (an
// index covers only the keys not named in the type — skjs-rules.md "Index
// Signatures"). The FIXME(closed-literals) markers pin behavior that the
// closed-object-literal redesign will flip.
// ============================================================================

// FIXME(closed-literals): should be accepted — the literal provably lacks
// `a`, and readonly `a?` grants no write capability; the rejection comes
// from the optional-field leg constraining the literal's synthetic index
// TVar before the never-index check runs.
function testEmptyVsReadonlyOptionalNeverIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {};
}

function testProvidedOptionalNeverIndex(): void {
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {
    a: 1,
  };
}

function testExcessVsNeverIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { readonly a?: number; [k: string]: never; [s: symbol]: never } = {
    a: 1,
    b: 2,
  };
}

// FIXME(closed-literals): should be accepted — single-view annotation; the
// annotation governs the value afterwards, and ownership transfer waives the
// never-index setter obligation for the fresh literal.
function testEmptyVsMutableOptionalNeverIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { a?: number; [k: string]: never; [s: symbol]: never } = {};
}

// FIXME(closed-literals): should be accepted — same as
// testEmptyVsReadonlyOptionalNeverIndex with a number index.
function testEmptyVsReadonlyOptionalNumberIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { readonly a?: string; [k: string]: number } = {};
}

// FIXME(closed-literals): should be accepted — the number-index check reuses
// the literal's string index slot.
function testEmptyVsReadonlyOptionalNumberNeverIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: {
    readonly a?: number;
    [k: string]: never;
    [n: number]: never;
    [s: symbol]: never;
  } = {};
}

// Aliasing defense: a mutable optional view may write number at "a"; a later
// boolean-index view would read it as boolean. Must stay rejected.
function testAliasMutableOptionalThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: { [k: string]: boolean } = t;
}

// Readonly view then mutable-index view of the same local. Rejected today
// (TVar poisoning) and still rejected under the redesign (after the first
// view transfers, the second is plain-checked: named-field-no-index rule).
function testAliasReadonlyOptionalThenIndex(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: { [k: string]: boolean } = t;
}

function testAliasMutableOptionalThenOptional(): void {
  const t = {};
  const f: { a?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: { b?: string } = t;
}

// FIXME(closed-literals): UNSOUND acceptance on the current base — b's view
// seals nothing usable, c grants write capability number at "a"; c can write
// t.a = 5 and a read through b types it `never`. Must become an error on the
// second view (after b's transfer, `{[k:string]: never} <: {a?: number}`
// fails the setter direction: number is not assignable into a never index).
function testAliasNeverIndexThenMutableOptional(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  const c: { a?: number } = t;
}

// Two readonly optional views: rejected today (poisoning); stays rejected
// under the redesign (after transfer to f's type, g's optional field b is
// missing and f's type has no index) — conservative but sound.
function testAliasTwoReadonlyOptionals(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: { readonly b?: string } = t;
}

// FIXME(closed-literals): UNSOUND acceptance on the current base — h's
// mutable `a?: number | string` grants writing a string at "a"; i reads "a"
// as number. Under the redesign the error appears at h (after f's transfer,
// `{a?: number} <: {a?: number | string}` fails the setter direction).
function testAliasWidenedGrantThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  const h: { a?: number | string } = t;
  const i: { [k: string]: number } = t;
}

declare const sk: unique symbol;

function testEmptyVsReadonlySymbolOptionalNeverIndex(): void {
  const x: {
    readonly [sk]?: number;
    [k: string]: never;
    [s: symbol]: never;
  } = {};
}

// Accepted on the current base only via the string/symbol leg-ordering
// asymmetry; stays accepted under the redesign for the principled reason
// (single-view annotation + ownership transfer).
function testEmptyVsMutableSymbolOptionalNeverIndex(): void {
  const x: { [sk]?: number; [k: string]: never; [s: symbol]: never } = {};
}

function testAliasMutableSymbolOptionalThenIndex(): void {
  const t = {};
  const f: { [sk]?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: { [s: symbol]: string } = t;
}

// ============================================================================
// Pins for behaviors the closed-literal redesign must preserve or knowingly
// change (probes beyond the optional-field matrix).
// ============================================================================

// Must stay accepted: fresh literal to a MUTABLE indexed annotation (the one
// thing synthetic indexes genuinely deliver; becomes ownership transfer).
function testFreshLiteralToMutableIndex(): void {
  const a: { [k: string]: number } = { x: 1, y: 2 };
}

// Must stay accepted: nested fresh literal against a nested-index annotation.
function testNestedFreshLiteralToIndex(): void {
  const x: { inner: { [j: string]: number } } = { inner: { a: 1 } };
}

// Must stay accepted: field-driven generic inference from a literal.
declare function takeFieldT<T>(x: { a: T }): T;
function testFieldDrivenInference(): number {
  return takeFieldT({ a: 1 });
}

// Spread literal of a no-index source to an indexed target: rejected on the
// current base and stays rejected (the spread source is width-open; its
// hidden keys are unknown). tsc accepts this unsoundly.
function testSpreadLiteralToIndex(src: { b: boolean }): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { [k: string]: boolean } = { ...src };
}

// Array of fresh literals to Array<indexed>: accepted on the current base.
// FIXME(closed-literals): may conservatively flip to reject in the redesign
// (array elements commit inside inference where no transfer runs); if so,
// the `as` workaround applies and this pin must be updated deliberately.
function testArrayOfLiteralsToArrayOfIndexed(): void {
  const arr: Array<{ [k: string]: number }> = [{ x: 1 }];
}

// Same mutable view inside a branch and again after it: accepted on the
// current base (TVars admit repeating an identical view).
// FIXME(closed-literals): becomes a conservative reject after the branch
// (the branch transfer merges with the closed type at the join); revisit
// with the shared-cell extension if the ergonomics matter.
function testSameViewInBranchThenAfter(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  }
  const g: { [k: string]: number } = t;
}

// View of an outside-declared local inside a loop: accepted on the current
// base and stays accepted (one-shot transparent check; no retype in loops).
function testViewInsideLoop(): void {
  const t = {};
  for (const i of [1, 2]) {
    const f: { [k: string]: number } = t;
  }
}

// ============================================================================
// Aliasing soundness witnesses: a granted view must be recorded somewhere.
// On the current base both are rejected because a literal field's get and
// set share one bound TVar — granting a wider view widens the read type too.
// Any redesign of literal typing must keep BOTH rejected.
// ============================================================================

// An embedded local keeps its own precise binding: if a view of the
// container grants index writes into it, reading `e.x` at its literal type
// would be unsound (o.a.x = 99; e.x : 1 holding 99).
function testEmbeddedLocalThenContainerView(): void {
  const e = { x: 1 };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const o: { a: { [k: string]: number } } = { a: e };
  o.a.x = 99;
  const z: 1 = e.x;
}

// A view granted inside a loop cannot be recorded by retyping (the local is
// declared outside); the write through the view would invalidate the
// precise post-loop read (f.x = 99; t.x : 1 holding 99).
function testThroughLoopViewThenPreciseRead(): void {
  const t = { x: 1 };
  for (const i of [1, 2]) {
    const f: { [k: string]: number } = t;
    f.x = 99;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: 1 = t.x;
}
