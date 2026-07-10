// Closed<T>: SKJS-specific closed-object type constructor (baseline).
//
// `Closed<T>` closes an object type: every key not named in T is provably
// absent (encoded as never string/symbol index signatures; SKJS indexes are
// residual, so the never indexes cover exactly the unnamed keys). For tsc
// compatibility, users declare the identity alias below — tsc sees plain T,
// SKJS gives the name its closed semantics (the builtin takes precedence for
// the 1-ary application).
//
// This file is the tests-first BASELINE: it is annotated for CURRENT main
// behavior, where the alias is a plain identity alias. `TODO(Closed)` marks
// the lines the feature flips.
type Closed<T> = T;

type Json = number | string | boolean | null | { readonly [k: string]: Json };

// ============================================================================
// The goal: a Closed object type is assignable to Json's readonly-index
// object branch (its unnamed keys are provably absent).
// ============================================================================

function testClosedIntoJson(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // TODO(Closed): the identity alias leaves x open, so this rejects today;
  // the Closed builtin removes the error below.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const j: Json = x;
}

function testNestedClosedIntoJson(): void {
  const x: Closed<{
    readonly a: number;
    readonly nested: Closed<{ readonly b: string }>;
  }> = { a: 1, nested: { b: "s" } };
  // TODO(Closed): the identity alias leaves x open, so this rejects today;
  // the Closed builtin removes the error below.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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

// Closed into a READONLY index: accepted once Closed is real (never getter
// under a readonly index imposes nothing).
function testClosedIntoReadonlyIndex(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
  // TODO(Closed): the identity alias leaves x open, so this rejects today;
  // the Closed builtin removes the error below.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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

// Excess property in a literal against a Closed annotation: SKJS's identity
// alias accepts the width today (tsc rejects via its fresh-literal excess
// check, TS2353); the closed never index rejects it.
function testExcessPropertyVsClosed(): void {
  // TODO(Closed): SKJS accepts the excess `b` today; Closed rejects it.
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

// ============================================================================
// keyof: Closed<T> adds no keys — keyof Closed<T> = keyof T.
// ============================================================================

function testKeyofClosed(): void {
  const k: keyof Closed<{ a: number }> = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const k2: keyof Closed<{ a: number }> = "b";
}

// ============================================================================
// Validation: Closed<T> requires a plain object type without index
// signatures. On main the identity alias accepts everything below.
// ============================================================================

function testClosedOfPrimitive(): void {
  // TODO(Closed): identity alias accepts; Closed requires an object type.
  const n: Closed<number> = 1;
}

function testClosedOfIndexedObject(): void {
  // TODO(Closed): identity alias accepts; Closed requires no existing index.
  const i: Closed<{ [k: string]: number }> = { a: 1 };
}

function testClosedOfUnion(): void {
  // TODO(Closed): identity alias accepts; Closed requires a single object type.
  const u: Closed<{ a: number } | { b: string }> = { a: 1 };
}

function testClosedOfTypeParameter<T>(x: Closed<T>): T {
  // TODO(Closed): identity alias accepts; Closed requires a statically known
  // object type, so an abstract type parameter is rejected.
  return x;
}
