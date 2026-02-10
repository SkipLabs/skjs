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
// Test 14: Nested index signatures
///////////////////////////////////////////////////////////////////////////////

type NestedIndex = { [k: string]: { [j: string]: number } };

function nestedIndexAccess(
  x: NestedIndex,
): { [j: string]: number } | undefined {
  return x["outer"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 15: Index signature with union value type
///////////////////////////////////////////////////////////////////////////////

type UnionValueIndex = { [k: string]: number | string };

function unionValueIndexAccess(
  x: UnionValueIndex,
): number | string | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 16: Recursive type with index signature
///////////////////////////////////////////////////////////////////////////////

type Json = string | number | boolean | null | Json[] | { [key: string]: Json };

function jsonAccess(x: Json): void {
  if (typeof x === "object" && x !== null && !Array.isArray(x)) {
    const val: Json | undefined = x["key"];
  }
}

///////////////////////////////////////////////////////////////////////////////
// Test 17: Index access with dynamic key
///////////////////////////////////////////////////////////////////////////////

function dynamicStringKey(x: StringIndex, key: string): number | undefined {
  return x[key];
}

function dynamicNumberKey(x: NumberIndex, key: number): string | undefined {
  return x[key];
}

///////////////////////////////////////////////////////////////////////////////
// Test 18: Invalid index key (wrong type of key used to access)
///////////////////////////////////////////////////////////////////////////////

function numberKeyOnStringIndex(x: StringIndex): number | undefined {
  return x[42];
}

function stringKeyOnNumberIndex(x: NumberIndex): void {
  // @skjs-expect-error Invalid index key
  const v = x["name"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 19: Valid union key types
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
// Test 20: Type alias as index key type
///////////////////////////////////////////////////////////////////////////////

type MyString = string;
type AliasIndex = { [k: MyString]: number };

function aliasIndexAccess(x: AliasIndex): number | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 21: Invalid key types (all rejected)
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
// Test 22: Cross-key-kind assignability (number is subtype of string)
///////////////////////////////////////////////////////////////////////////////

type NumberIndexNum = { [k: number]: number };
type StringIndexNum = { [k: string]: number };

// Number index assignable to string index (number keys are a subset of string keys)
function assignNumberIndexToStringIndex(x: NumberIndexNum): StringIndexNum {
  return x;
}

// String index NOT assignable to number index
function assignStringIndexToNumberIndex(x: StringIndexNum): NumberIndexNum {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 23: Named field types must be subtypes of index value type
///////////////////////////////////////////////////////////////////////////////

// Field type incompatible with string index value type
// @skjs-expect-error Property 'name' is not assignable to index value type
type FieldIncompatString = { name: string; [k: string]: number };

// Field type IS subtype of index value type — OK
type FieldCompatString = { name: string; [k: string]: string | number };

// Field type matches exactly — OK
type FieldExactMatch = { name: number; [k: string]: number };

// Multiple fields, one incompatible
// @skjs-expect-error Property 'b' is not assignable to index value type
type MultiFieldOneBad = { a: number; b: string; [k: string]: number };

// Named field with number-only index — no constraint (name isn't numeric)
type FieldWithNumberIndex = { name: string; [k: number]: boolean };

// Numeric field name with number index — must be compatible
// @skjs-expect-error Property '0' is not assignable to index value type
type NumericFieldBadNumberIndex = { 0: string; [k: number]: number };

// Numeric field name with number index — compatible, OK
type NumericFieldGoodNumberIndex = { 0: number; [k: number]: number };

// Named field with symbol index — no constraint, OK
type FieldWithSymbolIndex = { name: string; [k: symbol]: number };

// Symbol field incompatible with symbol index
declare const symBad: unique symbol;
// @skjs-expect-error Symbol property is not assignable to index value type
type SymbolFieldBadSymbolIndex = { [symBad]: string; [k: symbol]: number };

// Symbol field compatible with symbol index — OK
declare const symGood: unique symbol;
type SymbolFieldGoodSymbolIndex = { [symGood]: number; [k: symbol]: number };

///////////////////////////////////////////////////////////////////////////////
// Test 24: Cross-index validation (number index value must be subtype of string index value)
///////////////////////////////////////////////////////////////////////////////

// Number index value assignable to string index value — OK
type CrossIndexOk = { [k: string]: number | string; [k: number]: number };

// Number index value NOT assignable to string index value
// @skjs-expect-error Number index type is not assignable to string index type
type CrossIndexBad = { [k: string]: number; [k: number]: string };

// String and symbol indexes are independent — OK
type StringSymbolIndependent = { [k: string]: number; [k: symbol]: string };

// Number and symbol indexes are independent — OK
type NumberSymbolIndependent = { [k: number]: number; [k: symbol]: string };

///////////////////////////////////////////////////////////////////////////////
// Test 25: Duplicate/overlapping index signatures
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error Duplicate index signature
type DupStringIndex = { [k: string]: number; [k: string]: string };

// Interface with incompatible field
interface InterfaceFieldIncompat {
  // @skjs-expect-error Property 'name' is not assignable to index value type
  name: string;
  [k: string]: number;
}
