// Test: object literal assigned to indexed type
function testObjLiteralToIndexed(): void {
  const a: { [k: string]: number } = { x: 1, y: 2 };
}

// Test: dual assignment to different indexed types (second should fail)
function testDualIndexedAssignment(): void {
  const a = {};
  const b: { [k: string]: number } = a;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
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
// Signatures"). A no-spread object literal is a closed object; main accepts a
// fresh, single-view object literal against these closed/residual-index types
// via its existing subtyping (the implicit index of a fresh literal).
//
// The SECOND-VIEW INDEX GATE (this PR) additionally rejects the aliasing hazard
// where an already-used — or loop-escaping — unannotated local object is viewed
// AGAIN at an index-signature type: that second view grants a conflicting index
// capability over a value another view already constrained, so a write through
// one alias is observed at the wrong type through the other. Cases it does not
// cover (named-named same-key widening, generic-escaped index) keep `TODO(#678)`
// markers for the closed-object-literal redesign / a per-key extension.
// ============================================================================

// Accepted: the fresh literal `{}` satisfies the annotation directly — the
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

// Accepted: a fresh single-view literal `{}` has no keys, so the never index
// has nothing to reject; the annotation governs the value afterwards.
function testEmptyVsMutableOptionalNeverIndex(): void {
  const x: { a?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Accepted: same as testEmptyVsReadonlyOptionalNeverIndex with a number
// index value.
function testEmptyVsReadonlyOptionalNumberIndex(): void {
  const x: { readonly a?: string; [k: string]: number } = {};
}

// Accepted: a fresh single-view literal `{}` has no keys for the number index
// to constrain.
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
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: boolean } = t;
}

// Readonly view then mutable-index view of the same local: the first view uses
// `t`; the second, an index view of the now-used local, is rejected by the
// second-view index gate — a boolean index over the same keys `f` reads as
// number would let a write through one alias be read at the wrong type through
// the other.
function testAliasReadonlyOptionalThenIndex(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: boolean } = t;
}

// Accepted: two named optional views of disjoint keys (`f` only `a`, `g` only
// `b`). Neither targets an index type, so the second-view gate never fires, and
// disjoint keys mean there is no aliasing hazard — sound to accept.
function testAliasMutableOptionalThenOptional(): void {
  const t = {};
  const f: { a?: number } = t;
  const g: { b?: string } = t;
}

// `b` views `t` at a never index; `c` then writes `a: number` where `b`'s never
// index forbids any inhabited value — unsound. NOT caught by the second-view
// index gate: `c`'s target is a named optional, not an index, so the gate does
// not fire; catching it needs per-key recording of `b`'s grant.
function testAliasNeverIndexThenMutableOptional(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  // TODO(#678): still accepted — needs per-key recording of the prior never-index view.
  const c: { a?: number } = t;
}

// Two readonly optional views of disjoint keys: accepted. Neither targets an
// index type (the gate never fires) and both are pure reads of disjoint keys,
// so there is no aliasing hazard — sound to accept.
function testAliasTwoReadonlyOptionals(): void {
  const t = {};
  const f: { readonly a?: number } = t;
  const g: { readonly b?: string } = t;
}

// `f` grants a mutable `a?: number`. The index view `i` of the now-used local
// is rejected by the second-view index gate. The widened same-key named view
// `h` is NOT caught — both `f` and `h` are named views with no index, so the
// gate (which keys on index-typed views) does not fire; distinguishing `h` from
// a sound disjoint-key view needs per-key recording, so it stays TODO(#678).
function testAliasWidenedGrantThenIndex(): void {
  const t = {};
  const f: { a?: number } = t;
  // TODO(#678): still accepted — named-named same-key widening needs per-key recording.
  const h: { a?: number | string } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
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

// Accepted, uniformly with testEmptyVsMutableOptionalNeverIndex: a fresh
// single-view literal `{}` has no symbol keys for the never symbol index to
// reject.
function testEmptyVsMutableSymbolOptionalNeverIndex(): void {
  const x: { [sk]?: number; [k: string]: never; [s: symbol]: never } = {};
}

// Symbol analog: after the symbol-optional view uses `t`, the symbol-index view
// `g` is rejected by the second-view index gate.
function testAliasMutableSymbolOptionalThenIndex(): void {
  const t = {};
  const f: { [sk]?: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [s: symbol]: string } = t;
}

// ============================================================================
// Probes beyond the optional-field matrix: fresh-literal / local-object index
// views the second-view gate must preserve or knowingly change.
// ============================================================================

// Fresh literal to a MUTABLE indexed annotation: accepted — a fresh single-view
// object literal keeps main's implicit index (the second-view gate never fires
// on a literal RHS, only on a by-reference view of a tracked local).
function testFreshLiteralToMutableIndex(): void {
  const a: { [k: string]: number } = { x: 1, y: 2 };
}

// Conservative over-rejection (a documented limitation of the gate, not a
// soundness requirement). The gate keys on LOUsed, which cannot distinguish a
// benign read from a capability-granting view: any prior use of `t` — here just
// passing it to a function — trips the gate, so the later index view is rejected
// even though this single index view alone would be sound (cf.
// testDualIndexedAssignment, where the first index view is accepted). tsc
// accepts this; SKJS rejects it, consistent with its sound-stricter-than-tsc
// stance.
declare function readOnce<T>(x: T): void;
function testBenignReadThenIndexViewOverRejects(): void {
  const t = {};
  readOnce(t);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: number } = t;
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

// Array of fresh literals to Array<indexed>: accepted — each element is a fresh
// single-view object literal, not a by-reference view of a tracked local, so
// the second-view gate never fires.
function testArrayOfLiteralsToArrayOfIndexed(): void {
  const arr: Array<{ [k: string]: number }> = [{ x: 1 }];
}

// Same index view inside a branch and again after it: the in-branch view `f`
// records its index view on `t`, and the post-branch view `g` is a compatible
// repeat (`prevView <: annot`), so both are accepted soundly.
function testSameViewInBranchThenAfter(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  }
  const g: { [k: string]: number } = t;
}

// ============================================================================
// Multi-view matrix for #1056: compatible vs. conflicting repeated index views
// of a tracked local object across branches, sequences, mutability, mutations,
// and key kinds.
// ============================================================================

type NumMap = { [k: string]: number };

// Conflicting index view inside a branch and after it: must stay rejected
// (when `c` is true, writing through `g` as string corrupts `f`'s number view).
function testConflictingViewInBranchThenAfter(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: string } = t;
}

// Identical index view in two sibling branches: accepted.
function testSameViewInSiblingBranches(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  } else {
    const g: { [k: string]: number } = t;
  }
}

// Conflicting index view in sibling branches: still rejected conservatively
// (the gate tracks a single recorded index view per tracked local).
function testConflictingViewInSiblingBranches(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 But this object has already been used here
    const g: { [k: string]: string } = t;
  }
}

// Sequential identical index views: accepted.
function testSequentialSameView(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  const g: { [k: string]: number } = t;
}

// Sequential identical index views where one uses a type alias: accepted.
function testSequentialSameViewViaAlias(): void {
  const t = {};
  const f: NumMap = t;
  const g: { [k: string]: number } = t;
}

// Mutable index view followed by a readonly view of the same type: sound
// (`{ [k: string]: number } <: { readonly [k: string]: number }`).
function testMutableThenReadonlySame(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  const g: { readonly [k: string]: number } = t;
}

// Mutable index view followed by a wider readonly view: sound (writes through
// `f` produce `number`, which `g` soundly reads as `number | string`).
function testMutableThenReadonlyWider(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  const g: { readonly [k: string]: number | string } = t;
}

// Mutable index view followed by a wider MUTABLE view: unsound — writing a
// string through `g` would corrupt `f`'s number view. Must stay rejected.
function testMutableThenMutableWider(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: number | string } = t;
}

// Readonly index view followed by a mutable view of the same type: rejected
// (the first view only established a readonly contract, not a writable one).
function testReadonlyThenMutableSame(): void {
  const t = {};
  const f: { readonly [k: string]: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: number } = t;
}

// Readonly index view followed by a wider mutable view: unsound — writing a
// string through `g` corrupts `f`'s number reads. Must stay rejected.
function testReadonlyThenMutableWider(): void {
  const t = {};
  const f: { readonly [k: string]: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: number | string } = t;
}

// Readonly index view followed by a wider readonly view: sound.
function testReadonlyThenReadonlyWider(): void {
  const t = {};
  const f: { readonly [k: string]: number } = t;
  const g: { readonly [k: string]: number | string } = t;
}

// Wider readonly index view followed by a narrower readonly view: unsound if
// a third alias or field write populates a `string`. Must stay rejected.
function testReadonlyWiderThenReadonlyNarrower(): void {
  const t = {};
  const f: { readonly [k: string]: number | string } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { readonly [k: string]: number } = t;
}

// Identical repeat with an existing field mutated between views (`t.x` stays
// `number` after the first view widens it, so `t.x = 2` is valid and the
// repeated view stays sound).
function testSameViewWithFieldMutationBetween(): void {
  const t = { x: 1 };
  const f: { [k: string]: number } = t;
  t.x = 2;
  const g: { [k: string]: number } = t;
}

// Identical repeat after a branch when `t` carries an initialized field.
function testSameViewInBranchWithFieldThenAfter(c: boolean): void {
  const t = { x: 1 };
  if (c) {
    const f: { [k: string]: number } = t;
  }
  const g: { [k: string]: number } = t;
}

// Three views: the first two match, the third conflicts and must still fail.
function testThreeViewsThirdConflicts(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [k: string]: number } = t;
  }
  const g: { [k: string]: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const h: { [k: string]: string } = t;
}

// Number index views: identical repeat is sound; string index covers number
// index, while number index does not cover string index.
function testSameNumberIndexView(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [n: number]: number } = t;
  }
  const g: { [n: number]: number } = t;
}

function testStringIndexThenNumberIndex(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  const g: { [n: number]: number } = t;
}

function testNumberIndexThenStringIndex(): void {
  const t = {};
  const f: { [n: number]: number } = t;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 But this object has already been used here
  const g: { [k: string]: number } = t;
}

// Symbol index view repeated after a branch: accepted.
function testSameSymbolIndexView(c: boolean): void {
  const t = {};
  if (c) {
    const f: { [s: symbol]: number } = t;
  }
  const g: { [s: symbol]: number } = t;
}

// First view outside a loop, identical repeat inside a loop: still rejected
// by the through-loop arm (preserving #1057's loop rule).
function testLoopViewAfterPriorSameView(): void {
  const t = {};
  const f: { [k: string]: number } = t;
  for (const i of [1, 2]) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 But this object is declared outside the loop
    const g: { [k: string]: number } = t;
  }
}

// Index view of an outside-declared local inside a loop: rejected by the
// second-view index gate's through-loop arm — the loop body could grant the
// index view on every iteration while the local keeps its own type, so the view
// is an unrecordable aliasing hazard. Declare the local inside the loop instead.
// TODO(#1057): build a soundness-breaking witness or keep this as a general rule.
function testViewInsideLoop(): void {
  const t = {};
  for (const i of [1, 2]) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 But this object is declared outside the loop
    const f: { [k: string]: number } = t;
  }
}

// ============================================================================
// Aliasing soundness witnesses that any literal-typing design must keep
// rejected: an embedded local viewed through its container, and a through-loop
// view of an outside-declared local. The second-view index gate rejects the
// through-loop case directly; the embedded-container case is rejected by the
// ordinary mutable-field subtype check.
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

// An index view inside a loop of an outside-declared local is rejected by the
// second-view gate's through-loop arm. Because the gate SKIPS the subtype check
// (rather than failing it), the setter direction never widens `t.x`, so the
// precise post-loop read `t.x : 1` stays sound.
function testThroughLoopViewThenPreciseRead(): void {
  const t = { x: 1 };
  for (const i of [1, 2]) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 But this object is declared outside the loop
    const f: { [k: string]: number } = t;
    f.x = 99;
  }
  const z: 1 = t.x;
}

// ============================================================================
// Fresh literal instantiating a generic (unaffected by the second-view gate,
// which only fires on annotated by-reference views of a tracked local).
// ============================================================================

type JsonRec = { [key: string]: JsonRec } | number | string;
declare function processJsonRec<T extends JsonRec>(x: T): T;

// Accepted with an INFERRED type argument: the literal instantiates the type
// parameter; there is no by-reference index view of a tracked local, so the
// second-view gate does not apply.
function testFreshLiteralToInferredJsonGeneric(): void {
  const r = processJsonRec({ name: "test", nested: { value: 42 } });
}

// Rejected with an EXPLICIT type argument: the explicit `{ name: string }` is
// checked directly against the constraint `T extends JsonRec` (TS2344), and a
// named object type is not a subtype of JsonRec. This is unrelated to the
// second-view index gate.
function testFreshLiteralToExplicitJsonGeneric(): void {
  // TODO(#678): main also emits the argument-assignability error below; the
  // redesign's ownership transfer suppresses it, leaving only the constraint error.
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error Type argument does not satisfy the constraint
  const r = processJsonRec<{ name: string }>({ name: "test" });
}

// A fresh literal escaping through a generic keeps main's implicit index, so a
// later index view of the result is still accepted. NOT caught by the
// second-view gate: `r` is a call result, not a tracked local object, so the
// gate never fires; catching it needs a separate escape-seal at the inference
// grow site.
declare function idObj<T>(x: T): T;
function testEscapedInferredLiteralStaysClosed(): void {
  const r = idObj({ x: 1 });
  // TODO(#678): still accepted — needs an escape-seal at the generic grow site.
  const v: { [k: string]: number } = r;
}
