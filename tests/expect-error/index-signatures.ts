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
// Test 12: Index signature in interface
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
  // FIXME: TS allows number keys on string-indexed types
  // @skjs-expect-error Invalid index key
  return x[42];
}

function stringKeyOnNumberIndex(x: NumberIndex): void {
  // @skjs-expect-error Invalid index key
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
