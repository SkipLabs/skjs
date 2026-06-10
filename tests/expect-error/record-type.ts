///////////////////////////////////////////////////////////////////////////////
// Tests for the generic Record<K, V> type and the underlying mapped-type
// expansion `{ [P in K]: V }`.
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Anonymous mapped types
///////////////////////////////////////////////////////////////////////////////

type StringMap<V> = { [P in string]: V };

function stringMapAccept(): StringMap<number> {
  return { x: 1, y: 2 };
}

function stringMapReject(): StringMap<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { x: "no" };
}

type NumberMap<V> = { [P in number]: V };

function numberMapAccept(): NumberMap<string> {
  return { 0: "a", 1: "b" };
}

type SymbolMap<V> = { [P in symbol]: V };

function symbolMapAccept(): SymbolMap<boolean> {
  return {};
}

// Literal-union K becomes named fields
type LitAB<V> = { [P in "a" | "b"]: V };

function litABAccept(): LitAB<number> {
  return { a: 1, b: 2 };
}

function litABMissingB(): LitAB<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 1 };
}

function litABWrongV(): LitAB<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 1, b: "no" };
}

// Numeric literal union
type Lit01<V> = { [P in 0 | 1]: V };

function lit01Accept(): Lit01<string> {
  return { 0: "a", 1: "b" };
}

// Mixed kinds: string | number | symbol → all three indexes
type AllKinds<V> = { [P in string | number | symbol]: V };

function allKindsAccept(): AllKinds<number> {
  return {};
}

// Empty union → no fields
type EmptyMap<V> = { [P in never]: V };

function emptyMapAccept(): EmptyMap<number> {
  return {};
}

// Optional modifier '?'
type LitOpt<V> = { [P in "a" | "b"]?: V };

function litOptAcceptEmpty(): LitOpt<number> {
  return {};
}

function litOptAcceptPartial(): LitOpt<number> {
  return { a: 1 };
}

function litOptAcceptAll(): LitOpt<number> {
  return { a: 1, b: 2 };
}

function litOptRejectWrongV(): LitOpt<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: "no" };
}

// '+?' modifier — same effect as '?'
type LitPlusOpt<V> = { [P in "a" | "b"]+?: V };

function litPlusOptAccept(): LitPlusOpt<number> {
  return {};
}

// '-?' modifier — required (default behavior, but explicitly stated)
type LitMinusOpt<V> = { [P in "a" | "b"]-?: V };

function litMinusOptMissing(): LitMinusOpt<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 1 };
}

///////////////////////////////////////////////////////////////////////////////
// Record<K, V> from the standard library
///////////////////////////////////////////////////////////////////////////////

function recordStringAccept(): Record<string, number> {
  return { x: 1, y: 2 };
}

function recordStringWrongV(): Record<string, number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { x: "no" };
}

function recordLiteralUnion(): Record<"a" | "b", number> {
  return { a: 1, b: 2 };
}

function recordLiteralUnionMissing(): Record<"a" | "b", number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 1 };
}

function recordSingleLitMissing(): Record<"a", number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return {};
}

function recordNumber(): Record<number, string> {
  return { 0: "a", 1: "b" };
}

function recordNumberAccess(x: Record<number, string>): string | undefined {
  return x[0];
}

function recordNumberStringAccess(x: Record<number, string>): string {
  // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
  return x.foo;
}

function recordSymbolAccept(): Record<symbol, boolean> {
  return {};
}

function recordAllKinds(): Record<string | number | symbol, number> {
  return {};
}

function recordNeverAccept(): Record<never, number> {
  return {};
}

// Record<string, T> ↔ StringRecord<T>
function recordToStringRecord(x: Record<string, number>): StringRecord<number> {
  return x;
}

function stringRecordToRecord(x: StringRecord<number>): Record<string, number> {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Unsupported shapes — should error clearly
///////////////////////////////////////////////////////////////////////////////

// K is itself a type parameter (abstract after substitution).
// @skjs-expect-error Mapped types with an abstract key type are not yet supported by SKJS
function recordAbstractK<K extends string>(): Record<K, number> {
  return {};
}

// Disallowed K kind
// @skjs-expect-error This mapped type key shape is not yet supported by SKJS
type BadKey<V> = { [P in boolean]: V };

function badKeyUse(): BadKey<number> {
  return {};
}

// V references P → poison alias surfaces a clear unbound-type error
// @skjs-expect-error Type SKJS_unsupported_key_type_reference_in_mapped_type_value not found
type Boxed<K extends string> = { [P in K]: { key: P } };

function boxedUse(): Boxed<"a"> {
  return { a: { key: "a" } };
}
