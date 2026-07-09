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
// Signatures"). A no-spread object literal is a closed object; a fresh
// literal's use (or the first view of an unannotated local object) is an
// OWNERSHIP TRANSFER that waives the literal's setter obligations, so a
// fresh literal satisfies these closed types.
//
// This file is the behavioral BASELINE for the closed-object-literal redesign
// (PR #678): it is annotated for CURRENT main behavior and is green on main.
// `TODO(#678)` markers flag the cases the redesign changes; the feature commits
// flip those annotations.
// ============================================================================

// Accepted: the fresh literal `{}` is transferred to the annotation; the
// never index has no keys to reject and the optional `a?` is absent.
function testEmptyVsReadonlyOptionalNeverIndex(): void {
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

// Accepted: ownership transfer waives the never-index setter obligation for
// the fresh literal; the annotation governs the value afterwards.
function testEmptyVsMutableOptionalNeverIndex(): void {
  const x: { a?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Accepted: same as testEmptyVsReadonlyOptionalNeverIndex with a number
// index value.
function testEmptyVsReadonlyOptionalNumberIndex(): void {
  const x: { readonly a?: string; [k: string]: number } = {};
}

// Accepted: the number-index leg reuses the literal's closed string index,
// whose obligations the transfer waives.
function testEmptyVsReadonlyOptionalNumberNeverIndex(): void {
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
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const g: { [k: string]: boolean } = t;
}

// Readonly view then mutable-index view of the same local: the first view
// transfers `t` to `{ readonly a?: number }`, so the second is plain-checked
// and rejected — a named-field type with no index of its own is not an
// index type.
function testAliasReadonlyOptionalThenIndex(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const g: { [k: string]: boolean } = t;
}

// Accepted: after f retypes `t`, g's optional `b` is satisfied by the closed
// marker (provably absent — #754's unconditional optional-omission). The two
// views grant writes to disjoint keys (f only `a`, g only `b`), so there is no
// aliasing hazard — sound to accept, and consistent with main's spread #754.
function testAliasMutableOptionalThenOptional(): void {
  const t = {};
  const f: { a?: number } = t;
  const g: { b?: string } = t;
}

// b transfers `t` to `{ [k: string]: never }`; c is then plain-checked and
// rejected — the mutable optional `a?` would let c write a number where b's
// never index forbids it. (This was an UNSOUND acceptance before the
// redesign: nothing recorded c's write grant.)
function testAliasNeverIndexThenMutableOptional(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const c: { a?: number } = t;
}

// Two readonly optional views: accepted. f retypes `t` to the intersection
// `{ readonly a?: number; [closed] }`, keeping the literal's closed marker
// where f names no index; g's optional `b` is then satisfied by that marker
// with no setter obligation (g is readonly). Both views are pure reads of
// disjoint keys, so there is no aliasing hazard — sound to accept.
function testAliasTwoReadonlyOptionals(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  const g: { readonly b?: string } = t;
}

// f transfers `t` to `{ a?: number }`; h then fails the setter direction
// (`number | string` is not writable where f reads `number`) and i fails
// the named-field-no-index rule. (This was an UNSOUND all-accept before the
// redesign: h could write a string that i read as number.)
function testAliasWidenedGrantThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const h: { a?: number | string } = t;
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
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

// Accepted, uniformly with testEmptyVsMutableOptionalNeverIndex: single-view
// ownership transfer waives the mutable optional symbol field's setter
// obligation against the never symbol index.
function testEmptyVsMutableSymbolOptionalNeverIndex(): void {
  const x: { [sk]?: number; [k: string]: never; [s: symbol]: never } = {};
}

function testAliasMutableSymbolOptionalThenIndex(): void {
  const t = {};
  const f: { [sk]?: number } = t;
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const g: { [s: symbol]: string } = t;
}

// ============================================================================
// Pins for behaviors the closed-literal redesign must preserve or knowingly
// change (probes beyond the optional-field matrix).
// ============================================================================

// Fresh literal to a MUTABLE indexed annotation: accepted via ownership
// transfer (the one capability the old synthetic-index TVars existed for).
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

// Array of fresh literals to Array<indexed>: accepted — an array literal is
// a transfer site too, and its fresh elements (behind FromArrayElement
// wrappers) are eligible for the transfer's waivers.
function testArrayOfLiteralsToArrayOfIndexed(): void {
  const arr: Array<{ [k: string]: number }> = [{ x: 1 }];
}

// Same mutable view inside a branch and again after it: the in-branch
// transfer merges with the closed type at the join, so the post-branch view
// is plain-checked and rejected. Known conservative limitation; revisit
// with a shared-cell extension if the ergonomics matter.
function testSameViewInBranchThenAfter(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  }
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const g: { [k: string]: number } = t;
}

// View of an outside-declared local inside a loop: rejected. The local
// cannot be retyped from inside the loop, so the granted view would go
// unrecorded — the check runs plain and the closed literal does not satisfy
// a mutable index. Declare the local inside the loop or annotate it.
function testViewInsideLoop(): void {
  const t = {};
  for (const i of [1, 2]) {
    // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
    const f: { [k: string]: number } = t;
  }
}

// ============================================================================
// Aliasing soundness witnesses: a granted view must be recorded somewhere.
// Under ownership transfer both stay rejected by construction: an embedded
// local's markers are not eligible at the container's transfer (only values
// behind freshness wrappers are), and through-loop views are plain-checked
// because the local cannot be retyped. Any literal-typing design must keep
// BOTH rejected.
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
// declared outside), so the view itself is rejected — otherwise the write
// through it would invalidate the precise post-loop read (f.x = 99;
// t.x : 1 holding 99).
function testThroughLoopViewThenPreciseRead(): void {
  const t = { x: 1 };
  for (const i of [1, 2]) {
    // TODO(#678): main accepts this view (redesign rejects it, keeping `t` precise).
    const f: { [k: string]: number } = t;
    f.x = 99;
  }
  // TODO(#678): on main the accepted loop view above widens `t`, so this precise
  // read fails; the redesign rejects the view and keeps `t` precise, so the error
  // below goes away.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: 1 = t.x;
}

// ============================================================================
// Transfer-into-inference pins: a fresh literal instantiating a generic.
// ============================================================================

type JsonRec = { [key: string]: JsonRec } | number | string;
declare function processJsonRec<T extends JsonRec>(x: T): T;

// Accepted with an INFERRED type argument: the raw marked literal type grows
// into the inference TVar; the markers stay strict (closed) in later plain
// checks, so no write capability leaks.
function testFreshLiteralToInferredJsonGeneric(): void {
  const r = processJsonRec({ name: "test", nested: { value: 42 } });
}

// Rejected with an EXPLICIT type argument: the explicit `{ name: string }` is
// checked directly against the constraint `T extends JsonRec` (TS2344), and a
// named object type is not a subtype of JsonRec. Ownership transfer only waives
// the literal argument's setter obligations against the instantiated parameter
// type; it does not bypass the type-argument constraint check.
function testFreshLiteralToExplicitJsonGeneric(): void {
  // TODO(#678): main also emits the argument-assignability error below; the
  // redesign's ownership transfer suppresses it, leaving only the constraint error.
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error Type argument does not satisfy the constraint
  const r = processJsonRec<{ name: string }>({ name: "test" });
}

// The value escaping through the generic stays CLOSED: a later mutable index
// view of the result is a plain check and rejects.
declare function idObj<T>(x: T): T;
function testEscapedInferredLiteralStaysClosed(): void {
  const r = idObj({ x: 1 });
  // TODO(#678): main accepts this; the closed-object-literal redesign rejects it.
  const v: { [k: string]: number } = r;
}
