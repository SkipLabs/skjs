///////////////////////////////////////////////////////////////////////////////
// Tests for the generic Record<K, V> type and the underlying mapped-type
// expansion `{ [P in K]: V }`.
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Anonymous mapped types
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error TODO fnIn
type StringMap<V> = { [P in string]: V };

function stringMapAccept(): StringMap<number> {
  return { x: 1, y: 2 };
}

function stringMapReject(): StringMap<number> {
  return { x: "no" };
}

// @skjs-expect-error TODO fnIn
type NumberMap<V> = { [P in number]: V };

function numberMapAccept(): NumberMap<string> {
  return { 0: "a", 1: "b" };
}

// @skjs-expect-error TODO fnIn
type SymbolMap<V> = { [P in symbol]: V };

function symbolMapAccept(): SymbolMap<boolean> {
  return {};
}

// Literal-union K becomes named fields
// @skjs-expect-error TODO fnIn
type LitAB<V> = { [P in "a" | "b"]: V };

function litABAccept(): LitAB<number> {
  return { a: 1, b: 2 };
}

function litABMissingB(): LitAB<number> {
  return { a: 1 };
}

function litABWrongV(): LitAB<number> {
  return { a: 1, b: "no" };
}

// Numeric literal union
// @skjs-expect-error TODO fnIn
type Lit01<V> = { [P in 0 | 1]: V };

function lit01Accept(): Lit01<string> {
  return { 0: "a", 1: "b" };
}

// Mixed kinds: string | number | symbol → all three indexes
// @skjs-expect-error TODO fnIn
type AllKinds<V> = { [P in string | number | symbol]: V };

function allKindsAccept(): AllKinds<number> {
  return {};
}

// Empty union → no fields
// @skjs-expect-error TODO fnIn
type EmptyMap<V> = { [P in never]: V };

function emptyMapAccept(): EmptyMap<number> {
  return {};
}

///////////////////////////////////////////////////////////////////////////////
// Record<K, V> from the standard library
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error Type Record not found
function recordStringAccept(): Record<string, number> {
  return { x: 1, y: 2 };
}

// @skjs-expect-error Type Record not found
function recordStringWrongV(): Record<string, number> {
  return { x: "no" };
}

// @skjs-expect-error Type Record not found
function recordLiteralUnion(): Record<"a" | "b", number> {
  return { a: 1, b: 2 };
}

// @skjs-expect-error Type Record not found
function recordLiteralUnionMissing(): Record<"a" | "b", number> {
  return { a: 1 };
}

// @skjs-expect-error Type Record not found
function recordSingleLitMissing(): Record<"a", number> {
  return {};
}

// @skjs-expect-error Type Record not found
function recordNumber(): Record<number, string> {
  return { 0: "a", 1: "b" };
}

// @skjs-expect-error Type Record not found
function recordNumberAccess(x: Record<number, string>): string | undefined {
  return x[0];
}

// @skjs-expect-error Type Record not found
function recordNumberStringAccess(x: Record<number, string>): string {
  return x.foo;
}

// @skjs-expect-error Type Record not found
function recordSymbolAccept(): Record<symbol, boolean> {
  return {};
}

// @skjs-expect-error Type Record not found
function recordAllKinds(): Record<string | number | symbol, number> {
  return {};
}

// @skjs-expect-error Type Record not found
function recordNeverAccept(): Record<never, number> {
  return {};
}

// Record<string, T> ↔ StringRecord<T>
// @skjs-expect-error Type Record not found
function recordToStringRecord(x: Record<string, number>): StringRecord<number> {
  return x;
}

// @skjs-expect-error Type Record not found
function stringRecordToRecord(x: StringRecord<number>): Record<string, number> {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Unsupported shapes — should error clearly
///////////////////////////////////////////////////////////////////////////////

// K is itself a type parameter (abstract after substitution)
// @skjs-expect-error Type Record not found
function recordAbstractK<K extends string>(): Record<K, number> {
  return {};
}

// Disallowed K kind
// @skjs-expect-error TODO fnIn
type BadKey<V> = { [P in boolean]: V };

function badKeyUse(): BadKey<number> {
  return {};
}

// V references P → poison alias surfaces a clear unbound-type error
// @skjs-expect-error TODO fnIn
type Boxed<K extends string> = { [P in K]: { key: P } };

function boxedUse(): Boxed<"a"> {
  return { a: { key: "a" } };
}
