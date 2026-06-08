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
  // @skjs-expect-error Invalid return type
  return x["a"];
}

function stringIndexDotMissUndefined(x: StringIndex): number {
  // @skjs-expect-error Invalid return type
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
  // @skjs-expect-error Invalid return type
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: Symbol index signature
///////////////////////////////////////////////////////////////////////////////

type SymbolIndex = { [k: symbol]: boolean };

function symbolIndexBracketAccess(x: SymbolIndex): boolean | undefined {
  const s: symbol = Symbol("key");
  // @skjs-expect-error Expected a unique symbol
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
  // @skjs-expect-error Invalid return type
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 6: Assignability — object literal to indexed type
///////////////////////////////////////////////////////////////////////////////

function assignObjectToStringIndex(): void {
  const x: StringIndex = { a: 1, b: 2 };
}

function assignBadObjectToStringIndex(): void {
  // @skjs-expect-error Invalid annotation
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
  // @skjs-expect-error Invalid return type
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
  // @skjs-expect-error Invalid return type
  return s;
}

// Wide value type NOT assignable to narrow value type
function wideToNarrow(w: StringIdxWide): StringIdxNum {
  // @skjs-expect-error Invalid return type
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
  // @skjs-expect-error Invalid return type
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
  // @skjs-expect-error Invalid return type
  return x[k];
}
