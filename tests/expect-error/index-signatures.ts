///////////////////////////////////////////////////////////////////////////////
// Test 1: Basic string index signature
///////////////////////////////////////////////////////////////////////////////

type StringIndex = { [k: string]: number };

function stringIndexBracketAccess(x: StringIndex): number | undefined {
  return x["a"];
}

function stringIndexDotAccess(x: StringIndex): number | undefined {
  return x.a;
}

function stringIndexBracketMissUndefined(x: StringIndex): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x["a"];
}

function stringIndexDotMissUndefined(x: StringIndex): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x.a;
}

///////////////////////////////////////////////////////////////////////////////
// Test 2: Basic number index signature
///////////////////////////////////////////////////////////////////////////////

type NumberIndex = { [k: number]: string };

function numberIndexBracketAccess(x: NumberIndex): string | undefined {
  return x[0];
}

function numberIndexBracketMissUndefined(x: NumberIndex): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: Symbol index signature
///////////////////////////////////////////////////////////////////////////////

type SymbolIndex = { [k: symbol]: boolean };

// A general `symbol` key resolves through the symbol index, like a non-literal
// string/number key through its own index (see Test 27 for the field union).
function symbolIndexBracketAccess(x: SymbolIndex): boolean | undefined {
  const s: symbol = Symbol("key");
  return x[s];
}

///////////////////////////////////////////////////////////////////////////////
// Test 4: Mixed named fields and string index
///////////////////////////////////////////////////////////////////////////////

type MixedStringIndex = { name: string; [k: string]: string | number };

// Readonly: no setter check, getter passes (string <: string | number)
type MixedStringIndexReadonly = {
  readonly name: string;
  readonly [k: string]: string | number;
};

function mixedReadonlyNamedFieldDot(x: MixedStringIndexReadonly): string {
  return x.name;
}

function mixedReadonlyNamedFieldBracket(x: MixedStringIndexReadonly): string {
  return x["name"];
}

function mixedReadonlyIndexAccess(
  x: MixedStringIndexReadonly,
): string | number | undefined {
  return x["other"];
}

function mixedNamedFieldDot(x: MixedStringIndex): string {
  return x.name;
}

function mixedNamedFieldBracket(x: MixedStringIndex): string {
  return x["name"];
}

function mixedIndexAccess(x: MixedStringIndex): string | number | undefined {
  return x["other"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 5: Mixed named fields and number index
///////////////////////////////////////////////////////////////////////////////

type MixedNumberIndex = { name: string; [k: number]: boolean };

function mixedNumberNamedFieldDot(x: MixedNumberIndex): string {
  return x.name;
}

function mixedNumberIndexAccess(x: MixedNumberIndex): boolean | undefined {
  return x[0];
}

function mixedNumberIndexMissUndefined(x: MixedNumberIndex): boolean {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 6: Assignability — object literal to indexed type
///////////////////////////////////////////////////////////////////////////////

function assignObjectToStringIndex(): void {
  const x: StringIndex = { a: 1, b: 2 };
}

function assignBadObjectToStringIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: StringIndex = { a: 1, b: "oops" };
}

///////////////////////////////////////////////////////////////////////////////
// Test 7: Assignability — indexed type to object with optional fields
///////////////////////////////////////////////////////////////////////////////

function assignStringIndexToOptional(x: StringIndex): { a?: number } {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 8: Bracket assignment on indexed type
///////////////////////////////////////////////////////////////////////////////

function bracketAssignOnStringIndex(x: StringIndex): void {
  x["newKey"] = 42;
}

function bracketAssignOnNumberIndex(x: NumberIndex): void {
  x[99] = "hello";
}

///////////////////////////////////////////////////////////////////////////////
// Test 9: for-in with indexed object
///////////////////////////////////////////////////////////////////////////////

function forInStringIndex(x: StringIndex): void {
  for (const k in x) {
    const s: string = k;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 10: for-of on indexed object should fail
///////////////////////////////////////////////////////////////////////////////

function forOfStringIndex(x: StringIndex): void {
  // @skjs-expect-error Invalid iterable type for for-of loop
  for (const v of x) {
    console.log(v);
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 11: keyof indexed type
///////////////////////////////////////////////////////////////////////////////

const koString: keyof StringIndex = "anything";
const koNumber: keyof NumberIndex = 42;

///////////////////////////////////////////////////////////////////////////////
// Test 12: StringRecord<V> utility type
///////////////////////////////////////////////////////////////////////////////

function stringRecordAccess(x: StringRecord<number>): number | undefined {
  return x["key"];
}

function assignStringRecordToStringIndex(x: StringRecord<number>): StringIndex {
  return x;
}

function assignStringIndexToStringRecord(x: StringIndex): StringRecord<number> {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 13: Index signature in interface
///////////////////////////////////////////////////////////////////////////////

interface StringIndexed {
  [k: string]: number;
}

function interfaceIndexAccess(x: StringIndexed): number | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 13: Nested index signatures
///////////////////////////////////////////////////////////////////////////////

type NestedIndex = { [k: string]: { [j: string]: number } };

function nestedIndexAccess(
  x: NestedIndex,
): { [j: string]: number } | undefined {
  return x["outer"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 14: Index signature with union value type
///////////////////////////////////////////////////////////////////////////////

type UnionValueIndex = { [k: string]: number | string };

function unionValueIndexAccess(
  x: UnionValueIndex,
): number | string | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 15: Recursive type with index signature
///////////////////////////////////////////////////////////////////////////////

type Json = string | number | boolean | null | Json[] | { [key: string]: Json };

function jsonAccess(x: Json): void {
  if (typeof x === "object" && x !== null && !Array.isArray(x)) {
    const val: Json | undefined = x["key"];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 16: Index access with dynamic key
///////////////////////////////////////////////////////////////////////////////

function dynamicStringKey(x: StringIndex, key: string): number | undefined {
  return x[key];
}

function dynamicNumberKey(x: NumberIndex, key: number): string | undefined {
  return x[key];
}

///////////////////////////////////////////////////////////////////////////////
// Test 17: Invalid index key (wrong type of key used to access)
///////////////////////////////////////////////////////////////////////////////

function numberKeyOnStringIndex(x: StringIndex): number | undefined {
  return x[42];
}

function stringKeyOnNumberIndex(x: NumberIndex): void {
  // @skjs-expect-error Invalid index key: expected number, got string
  const v = x["name"];
}

// "Infinity" / "-Infinity" / "NaN" are numeric property names a number key can
// produce (e.g. String(Infinity) === "Infinity"), so a string-literal access
// with one of them resolves through the number index, like in TypeScript.
function nonFiniteStringLiteralOnNumberIndex(
  x: NumberIndex,
): string | undefined {
  const a = x["Infinity"];
  const b = x["-Infinity"];
  return x["NaN"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 18: Valid union key types
///////////////////////////////////////////////////////////////////////////////

type StringOrNumberIndex = { [k: string | number]: number };

function stringOrNumberIndexWithString(
  x: StringOrNumberIndex,
): number | undefined {
  return x["a"];
}

function stringOrNumberIndexWithNumber(
  x: StringOrNumberIndex,
): number | undefined {
  return x[42];
}

type AllKeysIndex = { [k: string | number | symbol]: number };

///////////////////////////////////////////////////////////////////////////////
// Test 19: Type alias as index key type
///////////////////////////////////////////////////////////////////////////////

type MyString = string;
type AliasIndex = { [k: MyString]: number };

function aliasIndexAccess(x: AliasIndex): number | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 20: Invalid key types (all rejected)
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type NeverIndex = { [k: never]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type BooleanIndex = { [k: boolean]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type NullIndex = { [k: null]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type UndefinedIndex = { [k: undefined]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type StringOrBoolIndex = { [k: string | boolean]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type ObjectIndex = { [k: object]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type LiteralIndex = { [k: "a" | "b"]: number };

// @skjs-expect-error An index signature parameter type must be string, number, or symbol
type GenericIndex<K> = { [k: K]: number };

///////////////////////////////////////////////////////////////////////////////
// Test 21: Cross-key-kind index assignability
///////////////////////////////////////////////////////////////////////////////

interface StringIdxNum {
  [key: string]: number;
}
interface NumberIdxNum {
  [key: number]: number;
}

// TS: number-indexed NOT assignable to string-indexed (missing string index)
function numIdxToStrIdx(n: NumberIdxNum): StringIdxNum {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n;
}

// TS: string-indexed IS assignable to number-indexed
function strIdxToNumIdx(s: StringIdxNum): NumberIdxNum {
  return s;
}

///////////////////////////////////////////////////////////////////////////////
// Test 22: Value type widening in cross-kind assignability
///////////////////////////////////////////////////////////////////////////////

interface StringIdxWide {
  [key: string]: number | string;
}

// Narrow value type assignable to wide value type
function narrowToWide(s: StringIdxNum): StringIdxWide {
  // FIXME: TS accepts this (number is subtype of number | string)
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// Wide value type NOT assignable to narrow value type
function wideToNarrow(w: StringIdxWide): StringIdxNum {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return w;
}

///////////////////////////////////////////////////////////////////////////////
// Test 23: Field types must be compatible with index value types
///////////////////////////////////////////////////////////////////////////////

interface BadFieldIndex {
  [key: string]: number;
  x: string;
}

interface GoodFieldIndex {
  [key: string]: number;
  x: number;
}

interface BadDualIdx {
  [key: string]: string;
  [key: number]: number;
}

interface GoodDualIdx {
  [key: string]: number | string;
  [key: number]: number;
}

// Readonly: no setter check, getter passes (number <: number | string)
interface GoodDualIdxReadonly {
  readonly [key: string]: number | string;
  readonly [key: number]: number;
}

function goodDualIdxReadonlyString(
  x: GoodDualIdxReadonly,
): number | string | undefined {
  return x["key"];
}

function goodDualIdxReadonlyNumber(x: GoodDualIdxReadonly): number | undefined {
  return x[0];
}

// Numeric-named field must be compatible with number index
interface BadNumField {
  [key: number]: number;
  "0": string;
}

///////////////////////////////////////////////////////////////////////////////
// Test 24: Non-literal key reads union in the declared field types
//
// SKJS does not reject objects whose declared fields are incompatible with the
// index value type (TypeScript's TS2411 — see BadFieldIndex above). A
// non-literal key may resolve to such a field at runtime, so the read result
// must include the declared field types, not just the index value type. For
// objects that DO satisfy TS2411 the field types are subsumed by the index
// value type, so this is a no-op there.
///////////////////////////////////////////////////////////////////////////////

interface NonConformingStrIndex {
  [key: string]: boolean;
  a: number;
}

// A dynamic string key may hit `a`, so the read is `boolean | number`, not just
// `boolean` (plus `undefined` because the key might be absent).
function nonConformingDynamicStringKey(
  x: NonConformingStrIndex,
  k: string,
): boolean | number | undefined {
  return x[k];
}

// `boolean | undefined` alone is too narrow: it drops `number` from `a`.
function nonConformingDynamicStringKeyTooNarrow(
  x: NonConformingStrIndex,
  k: string,
): boolean | undefined {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x[k];
}

// A specific literal that names no declared field can only hit the index, so
// the declared field type must NOT leak in.
function nonConformingLiteralMissOnlyIndex(
  x: NonConformingStrIndex,
): boolean | undefined {
  return x["zzz"];
}

// A literal that names the declared field reads exactly that field's type.
function nonConformingLiteralHitsNamedField(x: NonConformingStrIndex): number {
  return x["a"];
}

interface NonConformingNumIndex {
  [key: number]: boolean;
  0: string;
  a: number;
}

// A dynamic number key reaches the numeric-named field `0` (`string`) but never
// the non-numeric field `a` — so the read is `boolean | string`, not
// `boolean | number | string`. (Returning the exact type pins the exclusion of
// `a`: were `number` included, this would be too narrow and error.)
function nonConformingDynamicNumberKey(
  x: NonConformingNumIndex,
  k: number,
): boolean | string | undefined {
  return x[k];
}

// A conforming object (satisfies TS2411): the field type is subsumed by the
// index value type, so unioning it in is a no-op — the read stays `number`.
interface ConformingStrIndex {
  [key: string]: number;
  a: 1;
}

function conformingDynamicStringKey(
  x: ConformingStrIndex,
  k: string,
): number | undefined {
  return x[k];
}

// A dynamic number key can be Infinity / -Infinity / NaN at runtime (e.g.
// String(Infinity) === "Infinity"), so a field with one of those names is
// reachable by a number key and its type must be unioned in (here `bigint`),
// even though such names are not finite numeric strings.
interface NonFiniteNumKeyField {
  [key: string]: boolean;
  Infinity: bigint;
  "-Infinity": bigint;
  NaN: bigint;
}

function nonFiniteNumberKeyReachesField(
  x: NonFiniteNumKeyField,
  k: number,
): boolean | bigint | undefined {
  return x[k];
}

function nonFiniteNumberKeyTooNarrow(
  x: NonFiniteNumKeyField,
  k: number,
): boolean | undefined {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x[k];
}

///////////////////////////////////////////////////////////////////////////////
// Test 25: A named-field object TYPE is not assignable to an index signature it
// does not declare — SOUND, and deliberately stricter than TypeScript (which is
// unsound here).
//
// Object types are open under width subtyping: a value typed `{ 0: number }`
// may at runtime carry extra numeric-keyed properties of unrelated types (it
// could be a `{ 0: number; 5: string }`). Treating it as `{ [k: number]:
// number }` would then let `x[5]` be read as a `number` while holding a string.
// TypeScript permits this assignment and is unsound as a result; SKJS rejects
// it. The same applies to string indexes (`{ a: number }` is not assignable to
// `{ [k: string]: number }`). Object-literal *values* are still accepted,
// because SKJS checks every concrete field of a literal against the index value
// type (synthetic index, TType.sk). To use a named type as an indexed type, add
// an explicit index signature so all keys become a checked constraint.
//
// The rejection is uniform across finite-numeric, non-finite-numeric, and
// non-numeric field names — which is also why the `indexForFieldName`
// non-finite-name detail (TType.sk) is unobservable: every case below is
// rejected before it could matter.
///////////////////////////////////////////////////////////////////////////////

// Finite-numeric field, type compatible with the index value type — still
// rejected, because the source type may carry other numeric-keyed properties.
function numericFieldTypeToNumberIndex(x: { 0: number }): {
  [k: number]: number;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Non-finite numeric property name ("Infinity"): same soundness rejection.
function nonFiniteFieldTypeToNumberIndex(x: { Infinity: number }): {
  [k: number]: number;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Non-numeric field: rejected too — the source may still carry numeric-keyed
// properties of unrelated types that the number index would mistype.
function nonNumericFieldTypeToNumberIndex(x: { abc: string }): {
  [k: number]: number;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// String index, compatible field type: rejected for the same width-subtyping
// reason (the value may carry extra string-keyed properties of other types).
function namedFieldTypeToStringIndex(x: { a: number }): {
  [k: string]: number;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 26: Non-literal-key WRITES check the declared field setters too
//
// `x[k] = v` with a non-literal key must be valid for whichever field `k` could
// name at runtime, so the assigned value is checked against the intersection of
// the index setter and every reachable declared-field setter — the write
// counterpart of the Test 24 read union.
///////////////////////////////////////////////////////////////////////////////

// `k` could be "a" (a number field), so a boolean is not a valid write even
// though it satisfies the boolean index: number & boolean is never.
function writeNonConformingFieldRejected(
  x: { a: number; [k: string]: boolean },
  k: string,
): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x[k] = true;
}

// Conforming object: the write must still satisfy the field type.
function writeConformingWrongType(
  x: { a: number; [k: string]: number },
  k: string,
): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x[k] = "no";
}

function writeConformingOk(
  x: { a: number; [k: string]: number },
  k: string,
): void {
  x[k] = 5;
}

// Number key reaches the numeric-named field `0` (number & boolean = never)...
function writeNumberKeyReachesNumericField(
  x: { 0: number; [k: number]: boolean },
  n: number,
): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x[n] = true;
}

// ...but a non-numeric field is unreachable by a number key, so the write only
// has to satisfy the index.
function writeNumberKeyIgnoresNonNumericField(
  x: { a: string; [k: number]: boolean },
  n: number,
): void {
  x[n] = true;
}

// A readonly field the key could name makes the write unsatisfiable (it might
// write through the readonly field). TypeScript accepts this (unsound).
function writeBlockedByReadonlyField(
  x: { readonly version: string; [k: string]: string },
  k: string,
): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x[k] = "v";
}

// Plain index with no conflicting declared field: the write is unaffected.
function writePlainIndexOk(x: { [k: string]: number }, k: string): void {
  x[k] = 5;
}

///////////////////////////////////////////////////////////////////////////////
// Test 27: Symbol index + named symbol fields — read union / write intersect
//
// A general `symbol` key is the symbol counterpart of a non-literal string or
// number key (Tests 24/26): it could name any declared symbol field OR the
// symbol index, so reads union the field getters with the index getter and
// writes intersect the setters. A specific unique symbol is a literal key: it
// names exactly that field, or falls back to the symbol index.
///////////////////////////////////////////////////////////////////////////////

const symA: unique symbol = Symbol("a");
const symB: unique symbol = Symbol("b");

// Read via a general symbol unions the named field type with the index type.
function symGeneralReadUnionsField(
  x: { [symA]: number; [k: symbol]: boolean },
  s: symbol,
): number | boolean | undefined {
  return x[s];
}

// `boolean | undefined` alone is too narrow: it drops `number` from `symA`.
function symGeneralReadTooNarrow(
  x: { [symA]: number; [k: symbol]: boolean },
  s: symbol,
): boolean | undefined {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x[s];
}

// A unique symbol that names no declared field falls back to the symbol index.
function symUniqueNotFieldUsesIndex(x: {
  [symA]: number;
  [k: symbol]: boolean;
}): boolean | undefined {
  return x[symB];
}

// A unique symbol that IS a declared field reads exactly that field's type.
function symUniqueFieldExact(x: {
  [symA]: number;
  [k: symbol]: boolean;
}): number {
  return x[symA];
}

// Write via a general symbol must satisfy the index AND every reachable field
// setter: number & boolean = never, so the write is rejected.
function symGeneralWriteRejected(
  x: { [symA]: number; [k: symbol]: boolean },
  s: symbol,
): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x[s] = true;
}

// A general symbol with no symbol index cannot be resolved (matches TS7053).
function symGeneralNoIndex(x: { [symA]: number }, s: symbol): void {
  // @skjs-expect-error Invalid access
  const v = x[s];
}
