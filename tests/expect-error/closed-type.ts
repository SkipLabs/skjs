// Closed<T>: SKJS-specific closed-object type constructor.
//
// `Closed<T>` closes an object type: every key not named in T is provably
// absent (encoded as never string/symbol index signatures; SKJS indexes are
// residual, so the never indexes cover exactly the unnamed keys). Closed is
// declared in the SKJS stubs as an alias of the reserved SKJS_Closed, which
// the checker gives the closed semantics; a tsc-only stub declaring
// `type SKJS_Closed<T> = T` makes tsc read Closed<T> as the identity.

type Json = number | string | boolean | null | { readonly [k: string]: Json };

// ============================================================================
// The goal: a Closed object type is assignable to Json's readonly-index
// object branch (its unnamed keys are provably absent).
// ============================================================================

function testClosedIntoJson(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  const j: Json = x;
}

function testNestedClosedIntoJson(): void {
  const x: Closed<{
    readonly a: number;
    readonly nested: Closed<{ readonly b: string }>;
  }> = { a: 1, nested: { b: "s" } };
  const j: Json = x;
}

// Open object types stay NOT assignable to Json (unknown hidden keys) — the
// soundness-required strictness Closed<T> exists to opt out of.
function testOpenIntoJsonStaysRejected(): void {
  const x: { readonly a: number } = { a: 1 };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const j: Json = x;
}

// ============================================================================
// Index-signature supertypes.
// ============================================================================

// Closed into a READONLY index: accepted (the never getter under a readonly
// index imposes nothing).
function testClosedIntoReadonlyIndex(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  const m: { readonly [k: string]: number } = x;
}

// Closed into a MUTABLE index: rejected both before (open source, missing
// index) and after (the index's write capability contradicts closedness).
function testClosedIntoMutableIndex(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const m: { [k: string]: number } = x;
}

// ============================================================================
// Closedness of values: excess properties and unnamed keys.
// ============================================================================

// Excess property in a literal against a Closed annotation: rejected by the
// closed never index (tsc also rejects, via its fresh-literal excess check).
function testExcessPropertyVsClosed(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: Closed<{ a?: number }> = { a: 1, b: 2 };
}

// An OPEN object value into a Closed target: rejected — the value may carry
// unknown extra keys (width subtyping); the diagnostic explains the target
// is closed rather than reporting a missing index signature.
function testOpenIntoClosedRejected(x: { readonly a: number }): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '{ readonly a: number; }'
  // @skjs-expect-error-line3 is not assignable to type 'Closed<{ readonly a: number; }>'
  // @skjs-expect-error-line4 The target is a closed object type: every unnamed key is provably absent, but the source is an open object type that may have unknown extra keys
  const c: Closed<{ readonly a: number }> = x;
}

// Reading an unnamed key: rejected (the key is provably absent).
function testReadUnnamedKey(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line3 The object type is closed: its unnamed keys are provably absent
  const v = x.b;
}

// Writing an unnamed key: rejected.
function testWriteUnnamedKey(): void {
  const x: Closed<{ a: number }> = { a: 1 };
  // @skjs-expect-error Property 'b' does not exist on this type
  x.b = 2;
}

// The named field keeps its own mutability.
function testNamedFieldStaysWritable(): void {
  const x: Closed<{ a: number }> = { a: 1 };
  x.a = 2;
}

declare const sym: unique symbol;

// Reading an unnamed symbol key: rejected (provably absent).
function testReadUnnamedSymbolKey(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // @skjs-expect-error This symbol property does not exist on the object
  // @skjs-expect-error-line2 The object type is closed: its unnamed keys are provably absent
  const v = x[sym];
}

// ============================================================================
// satisfies: Closed works as the expected type and retains field inference
// commitments from validation.
// ============================================================================

function testSatisfiesClosed(): void {
  const x = { a: 1 } satisfies Closed<{ readonly a: number }>;
  // Like tsc with an identity alias, the numeric target widens x.a.
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const one: 1 = x.a;
}

function testSatisfiesClosedExcess(): void {
  // @skjs-expect-error Type does not satisfy the expected type
  const x = { a: 1, b: 2 } satisfies Closed<{ readonly a: number }>;
}

// ============================================================================
// Interop: Object.keys/values/entries on a Closed value.
// ============================================================================

function testObjectKeysValuesEntriesOnClosed(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  const ks = Object.keys(x);
  const vals = Object.values(x);
  const ents = Object.entries(x);
}

// ============================================================================
// keyof: Closed<T> adds no keys — keyof Closed<T> = keyof T.
// ============================================================================

function testKeyofClosed(): void {
  const k: keyof Closed<{ a: number }> = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const k2: keyof Closed<{ a: number }> = "b";
}

// ============================================================================
// Validation: Closed<T> requires a statically known object type without
// declared index signatures.
// ============================================================================

function testClosedOfPrimitive(): void {
  // @skjs-expect-error Closed<T> requires a statically known object type
  const n: Closed<number> = 1;
}

function testClosedOfIndexedObject(): void {
  // @skjs-expect-error Closed<T> requires an object type without index signatures
  const i: Closed<{ [k: string]: number }> = { a: 1 };
}

// A union of object types distributes: each branch is closed independently.
function testClosedOfUnionDistributes(): void {
  const u: Closed<{ a: number } | { b: string }> = { a: 1 };
  const j: Json = u;
}

// An abstract type parameter is not a statically known object type.
function testClosedOfTypeParameter<T>(
  // @skjs-expect-error Closed<T> requires a statically known object type
  x: Closed<T>,
): T {
  return x;
}

// A CONSTRAINED type parameter is abstract too: rejected at the parameter
// (NOT silently closing the constraint).
function testClosedOfConstrainedTypeParameter<T extends { a: number }>(
  // @skjs-expect-error Closed<T> requires a statically known object type
  x: Closed<T>,
): T {
  return x;
}

// A generic alias wrapping Closed: validation of the abstract body is
// deferred during type-definition validation and performed when each concrete
// instantiation is expanded, anchoring errors at the use site (#814).
type FreezeWrapper<T> = Closed<T>;

function testClosedAliasWrapperConcrete(): void {
  const x: FreezeWrapper<{ readonly a: number }> = { a: 1 };
  const j: Json = x;
}

function testClosedAliasWrapperBadInstantiation(): void {
  // @skjs-expect-error Closed<T> requires a statically known object type
  const n: FreezeWrapper<number> = 1;
}

// A second bad instantiation of the same `FreezeWrapper<number>` must also
// anchor at its own use site even when the named-expansion cache hits.
function testClosedAliasWrapperBadInstantiationSecond(): void {
  // @skjs-expect-error Closed<T> requires a statically known object type
  const n: FreezeWrapper<number> = 2;
}

// Multi-level wrapper alias: errors still anchor at the outermost use site.
type DeepFreezeWrapper<T> = FreezeWrapper<T>;

function testClosedDeepWrapperConcrete(): void {
  const x: DeepFreezeWrapper<{ readonly a: number }> = { a: 1 };
  const j: Json = x;
}

function testClosedDeepWrapperBadInstantiation(): void {
  // @skjs-expect-error Closed<T> requires a statically known object type
  const n: DeepFreezeWrapper<number> = 1;
}

// Shallow closing preserves symbolic nested aliases without eager flattening:
// a field typed via a recursive alias stays symbolic inside Closed<...>.
type NestedTree = { readonly val: number; readonly child?: NestedTree };
type ClosedNestedHolder = Closed<{ readonly tree: NestedTree }>;

function testClosedShallowPreservesNestedAlias(): void {
  const leaf: NestedTree = { val: 1 };
  const holder: ClosedNestedHolder = { tree: leaf };
  const t: NestedTree = holder.tree;
  // @skjs-expect-error Property 'extra' does not exist on this type
  const bad = holder.extra;
}

// ============================================================================
// Additional validation & edge cases (SkipLabs/skjs#814):
// arrays/tuples, synthetic literal index replacement, recursive aliases,
// and idempotence (`Closed<Closed<T>>`, `Closed<typeof asConst>`).
// ============================================================================

function testClosedOfArray(): void {
  // @skjs-expect-error Closed<T> is not supported on array or tuple types
  const a: Closed<number[]> = [1];
}

function testClosedOfTuple(): void {
  // @skjs-expect-error Closed<T> is not supported on array or tuple types
  const t: Closed<[number, string]> = [1, "a"];
}

// Closing `typeof lit` (plain object literal carrying a synthetic index)
// replaces the synthetic index with never indexes.
function testClosedOfLiteralSyntheticIndex(): void {
  const lit = { a: 1, b: "s" };
  const ok: Closed<typeof lit> = { a: 1, b: "s" };
  const j: Json = ok;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Closed<typeof lit> = { a: 1, b: "s", c: 3 };
}

// Recursive alias directly through Closed<...> is circular (TS2456), not a loop.
// @skjs-expect-error Type alias 'SelfClosed' circularly references itself
type SelfClosed = Closed<SelfClosed>;

// Direct recursive alias through SKJS_Closed<...> is also circular (TS2456).
// @skjs-expect-error Type alias 'SelfDirectClosed' circularly references itself
type SelfDirectClosed = SKJS_Closed<SelfDirectClosed>;

// Nested `Closed<Closed<T>>` is idempotent (#814) and preserves `Closed<...>`
// display without double-wrapping.
function testClosedOfClosed(): void {
  const x: Closed<Closed<{ readonly a: number }>> = { a: 1 };
  const j: Json = x;
  __SKJS_show_expanded(x, "Closed<{ readonly a: number; }>");
}

type ClosedAlreadyObj = Closed<{ readonly a: number }>;

// `Closed<ClosedAlreadyObj>` is idempotent (#814).
function testClosedOfClosedAlias(): void {
  const x: Closed<ClosedAlreadyObj> = { a: 1 };
  const j: Json = x;
}

// Closing an already-closed `as const` literal is idempotent (#814).
function testClosedOfAsConst(): void {
  const lit = { a: 1 } as const;
  const x: Closed<typeof lit> = { a: 1 };
  const j: Json = x;
}

// Direct `SKJS_Closed<SKJS_Closed<T>>` is also idempotent (#814).
function testDirectClosedOfClosed(): void {
  const x: SKJS_Closed<SKJS_Closed<{ readonly a: number }>> = { a: 1 };
  const j: Json = x;
}

// ============================================================================
// Diagnostic display of Closed<T> (SkipLabs/skjs#803):
// Errors should print `Closed<...>` instead of the raw never-index encoding.
// ============================================================================

type ClosedNamedObj = { readonly a: number };

function testClosedDisplayIntoPrimitive(
  x: Closed<{ readonly a: number }>,
): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<{ readonly a: number; }>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

function testPrimitiveIntoClosedDisplay(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '42'
  // @skjs-expect-error-line3 is not assignable to type 'Closed<{ readonly a: number; }>'
  const c: Closed<{ readonly a: number }> = 42;
}

function testClosedNamedAliasDisplay(x: Closed<ClosedNamedObj>): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<ClosedNamedObj>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

function testClosedWrapperDisplay(
  x: FreezeWrapper<{ readonly a: number }>,
): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<{ readonly a: number; }>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

function testClosedUnionDisplay(
  x: Closed<{ a: number } | { b: string }>,
): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<{ a: number; } | { b: string; }>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

function testClosedEmptyDisplay(x: Closed<{}>): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<{}>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

interface ClosedRecursiveNode {
  readonly value: number;
  readonly next?: Closed<ClosedRecursiveNode>;
}

function testClosedRecursiveDisplay(x: Closed<ClosedRecursiveNode>): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'Closed<ClosedRecursiveNode>'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  const n: number = x;
}

function testClosedShowExpanded(): void {
  const direct: Closed<{ readonly a: number }> = { a: 1 };
  __SKJS_show_expanded(direct, "Closed<{ readonly a: number; }>");
  const named: Closed<ClosedNamedObj> = { a: 1 };
  __SKJS_show_expanded(named, "Closed<ClosedNamedObj>");
  const empty: Closed<{}> = {};
  __SKJS_show_expanded(empty, "Closed<{}>");
}

// ============================================================================
// Never-index vs. undeclared missing-property diagnostics (SkipLabs/skjs#803):
// Missing-property diagnostics distinguish a closed object (`Closed<T>` /
// `as const`), a key covered by a never-valued index signature (including an
// intersected index collapsed to `never`), and a plain undeclared key.
// ============================================================================

function testNeverNumberIndexNumericKey(x: {
  readonly a: number;
  [k: number]: never;
}): void {
  // Numeric key is covered by `[k: number]: never`: provably absent via never index.
  // @skjs-expect-error Property '0' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  // @skjs-expect-error-line3 This key is provably absent: its covering index signature is never
  const v = x[0];
}

function testNeverNumberIndexStringNumericKey(x: {
  readonly a: number;
  [k: number]: never;
}): void {
  // Numeric string key "0" is covered by `[k: number]: never`: provably absent.
  // @skjs-expect-error Property '0' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  // @skjs-expect-error-line3 This key is provably absent: its covering index signature is never
  const v = x["0"];
}

function testNeverNumberIndexNonNumericKey(x: {
  readonly a: number;
  [k: number]: never;
}): void {
  // Non-numeric key is not covered by `[k: number]: never`: stays a plain
  // missing-property error with no closed/never-index note.
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  const v = x.b;
}

function testNeverSymbolIndexStringKey(x: {
  readonly a: number;
  [k: symbol]: never;
}): void {
  // `[k: symbol]: never` does not cover string key `b`: plain missing property.
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  const v = x.b;
}

function testNeverStringIndexRead(x: {
  readonly a: number;
  [k: string]: never;
}): void {
  // Only string keys have a never index (not a Closed<T> object): report the
  // covering never-index note rather than claiming the whole object is closed.
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  // @skjs-expect-error-line3 This key is provably absent: its covering index signature is never
  const v = x.b;
}

function testClosedDestructuringMissingKey(
  x: Closed<{ readonly a: number }>,
): void {
  // Destructuring a missing key on a closed object explains that it is closed.
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line2 Out of 'Closed<{ readonly a: ...; }>'
  // @skjs-expect-error-line3 The object type is closed: its unnamed keys are provably absent
  const { b } = x;
}

function testNeverSymbolIndexSymbolKey(x: {
  readonly a: number;
  [k: symbol]: never;
}): void {
  // Symbol key covered by `[k: symbol]: never`: reports the never-index note.
  // @skjs-expect-error This symbol property does not exist on the object
  // @skjs-expect-error-line2 This key is provably absent: its covering index signature is never
  const v = x[sym];
}

function testUnionClosedAndOpenMissingKey(
  x: Closed<{ readonly a: number }> | { readonly a: number },
): void {
  // Union of a closed branch and an open branch: the whole type is not closed,
  // but the closed branch's covering never index proves the key absent there.
  // @skjs-expect-error Property 'b' does not exist on this type
  // @skjs-expect-error-line2 Possible options are:
  // @skjs-expect-error-line3 This key is provably absent: its covering index signature is never
  const v = x.b;
}
