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

// Reading an unnamed key: rejected (the key is provably absent).
function testReadUnnamedKey(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // @skjs-expect-error Property 'b' does not exist on this type
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
  const v = x[sym];
}

// ============================================================================
// satisfies: Closed works as the expected type; the value keeps its precise
// literal type.
// ============================================================================

function testSatisfiesClosed(): void {
  const x = { a: 1 } satisfies Closed<{ readonly a: number }>;
  // tsc (identity alias) widens x.a to number here; SKJS keeps the literal 1.
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
// deferred during type-definition validation and performed at each concrete
// instantiation instead, so wrappers work. A BAD concrete instantiation
// (testClosedAliasWrapperBadInstantiation below) reports here, at the
// wrapper's own Closed<T> application — the use-site position is erased by
// alias re-positioning before the instantiation-time check runs.
// @skjs-expect-error Closed<T> requires a statically known object type
type FreezeWrapper<T> = Closed<T>;

function testClosedAliasWrapperConcrete(): void {
  const x: FreezeWrapper<{ readonly a: number }> = { a: 1 };
  const j: Json = x;
}

function testClosedAliasWrapperBadInstantiation(): void {
  const n: FreezeWrapper<number> = 1;
}
