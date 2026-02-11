///////////////////////////////////////////////////////////////////////////////
// Test 1: Union of same-kind string index signatures
///////////////////////////////////////////////////////////////////////////////

type StrIdx1 = { [k: string]: number };
type StrIdx2 = { [k: string]: string };

// Value types are unioned: number | string | undefined
function unionStringIndexOk(x: StrIdx1 | StrIdx2): number | string | undefined {
  return x["a"];
}

function unionStringIndexTooNarrow(x: StrIdx1 | StrIdx2): number | undefined {
  // @skjs-expect-error Invalid return type
  return x["a"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 2: Union of same-kind number index signatures
///////////////////////////////////////////////////////////////////////////////

type NumIdx1 = { [k: number]: number };
type NumIdx2 = { [k: number]: string };

function unionNumberIndexOk(x: NumIdx1 | NumIdx2): number | string | undefined {
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: Union where one has index, other has named field
///////////////////////////////////////////////////////////////////////////////

type WithIdx = { [k: string]: number };
type WithField = { a: string };

// Both branches support ["a"]: WithIdx gives number|undefined, WithField gives string
function unionIdxAndFieldAccess(
  x: WithIdx | WithField,
): number | string | undefined {
  return x["a"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 4: Intersection of same-kind string index signatures
///////////////////////////////////////////////////////////////////////////////

// Intersection of value types: number & string = never, access gives never | undefined = undefined
function interStringIndex(
  x: { [k: string]: number } & { [k: string]: string },
): void {
  const v: number | string | undefined = x["a"];
  const v2: undefined = x["a"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 5: Intersection of index + named field
///////////////////////////////////////////////////////////////////////////////

function interIndexAndField(x: { [k: string]: number } & { a: string }): void {
  const v1: string = x.a;
  const v2: number | undefined = x["b"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 6: Intersection preserves named fields from both sides
///////////////////////////////////////////////////////////////////////////////

function interFieldsMerge(
  x: { a: number; [k: string]: number } & { b: string; [k: string]: string },
): void {
  const v1: number = x.a;
  const v2: string = x.b;
}

///////////////////////////////////////////////////////////////////////////////
// Test 7: Subtyping — string index value covariance
///////////////////////////////////////////////////////////////////////////////

// Narrower value type assignable to wider value type
function subStringValueOk(x: { [k: string]: number }): {
  [k: string]: number | string;
} {
  return x;
}

// Wider value type NOT assignable to narrower value type
function subStringValueFail(x: { [k: string]: number | string }): {
  [k: string]: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 8: Subtyping — number index value covariance
///////////////////////////////////////////////////////////////////////////////

function subNumberValueOk(x: { [k: number]: number }): {
  [k: number]: number | string;
} {
  return x;
}

function subNumberValueFail(x: { [k: number]: number | string }): {
  [k: number]: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 9: Subtyping — symbol index value covariance
///////////////////////////////////////////////////////////////////////////////

function subSymbolValueOk(x: { [k: symbol]: number }): {
  [k: symbol]: number | string;
} {
  return x;
}

function subSymbolValueFail(x: { [k: symbol]: number | string }): {
  [k: symbol]: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 10: Subtyping — named fields satisfy string index
///////////////////////////////////////////////////////////////////////////////

// All named fields are subtypes of index value type — OK
function subFieldsToStringIndex(x: { a: number; b: number }): {
  [k: string]: number;
} {
  return x;
}

// One named field is NOT subtype of index value type — FAIL
function subFieldsToStringIndexFail(x: { a: number; b: string }): {
  [k: string]: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 11: Subtyping — index to required named field (field missing)
///////////////////////////////////////////////////////////////////////////////

// String index does NOT satisfy a required named field
function subIdxToField(x: { [k: string]: number }): { a: number } {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 12: Subtyping — index + named fields to index
///////////////////////////////////////////////////////////////////////////////

// Sub has both index and named fields, super has just index — OK
function subIdxAndFieldsToIdx(x: { a: number; [k: string]: number }): {
  [k: string]: number;
} {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 13: Subtyping — number index to string index (fallback)
///////////////////////////////////////////////////////////////////////////////

// Number keys are subset of string keys — number index satisfies string index
function subNumberToString(x: { [k: number]: number }): {
  [k: string]: number;
} {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 14: Subtyping — cross-kind compatibility
///////////////////////////////////////////////////////////////////////////////

// String index covers numeric keys — satisfies number index
function subStringToNumber(x: { [k: string]: number }): {
  [k: number]: number;
} {
  return x;
}

// Symbol index is irrelevant to string keys — vacuously satisfies string index
function subSymbolToString(x: { [k: symbol]: number }): {
  [k: string]: number;
} {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 15: Subtyping — no index to number/symbol index (vacuously true)
///////////////////////////////////////////////////////////////////////////////

// Object with named fields but no index can satisfy number index requirement
function subNoIndexToNumber(x: { a: number }): { [k: number]: number } {
  return x;
}

// Object with named fields but no index can satisfy symbol index requirement
function subNoIndexToSymbol(x: { a: number }): { [k: symbol]: number } {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 16: Subtyping — combined string + number indexes
///////////////////////////////////////////////////////////////////////////////

// Sub has both string+number, super has just string — OK
function subBothToString(x: { [k: string]: number; [k: number]: number }): {
  [k: string]: number;
} {
  return x;
}

// String index covers numeric keys — satisfies both string and number index
function subStringToBoth(x: { [k: string]: number }): {
  [k: string]: number;
  [k: number]: number;
} {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 17: Union — indexed type + typed object, dot access
///////////////////////////////////////////////////////////////////////////////

type IdxObj = { [k: string]: number };
type FieldObj = { a: string; b: boolean };

// x.a: IdxObj gives number|undefined (string index), FieldObj gives string
function unionIdxAndFieldDot(
  x: IdxObj | FieldObj,
): number | string | undefined {
  return x.a;
}

// x.b: IdxObj gives number|undefined (string index), FieldObj gives boolean
function unionIdxAndFieldDotB(
  x: IdxObj | FieldObj,
): number | boolean | undefined {
  return x.b;
}

///////////////////////////////////////////////////////////////////////////////
// Test 18: Subtyping — sub has index + fields, super requires different fields
///////////////////////////////////////////////////////////////////////////////

// Index doesn't satisfy required named field
function subIdxFieldsToOtherFields(x: { a: number; [k: string]: number }): {
  a: number;
  b: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 19: Subtyping — sub has fields, super has index + field
///////////////////////////////////////////////////////////////////////////////

// Fields satisfy both the named field and the index constraint
function subFieldsToIdxAndField(x: { a: number; b: number }): {
  a: number;
  [k: string]: number;
} {
  return x;
}

// Field type incompatible with index value type in super
function subFieldsToIdxAndFieldFail(x: { a: number; b: string }): {
  a: number;
  [k: string]: number;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 20: Subtyping — sub has index, super has optional field
///////////////////////////////////////////////////////////////////////////////

// String index satisfies optional named field
function subIdxToOptionalField(x: { [k: string]: number }): { a?: number } {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 21: Subtyping — sub has index + wider field, super has narrower field
///////////////////////////////////////////////////////////////////////////////

function subIdxFieldWiderType(x: {
  a: number | string;
  [k: string]: number | string;
}): { a: number } {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Test 22: Intersection — index + fields from both sides
///////////////////////////////////////////////////////////////////////////////

function interIdxAndFieldsBothSides(
  x: { a: number; [k: string]: number } & { b: string },
): void {
  const v1: number = x.a;
  const v2: string = x.b;
  const v3: number | undefined = x["c"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 23: Union — field type should include other side's string index value
///////////////////////////////////////////////////////////////////////////////

// x.b: left has string index (number), right has field b (string)
// Result should be string | number | undefined, not just string | undefined
function unionFieldVsStringIdxNarrow(
  x: { [k: string]: number } | { b: string },
): string | undefined {
  // @skjs-expect-error Invalid return type
  return x.b;
}

function unionFieldVsStringIdxOk(
  x: { [k: string]: number } | { b: string },
): string | number | undefined {
  return x.b;
}

///////////////////////////////////////////////////////////////////////////////
// Test 24: Union — field on left, string index on right
///////////////////////////////////////////////////////////////////////////////

function unionFieldLeftIdxRightNarrow(
  x: { a: number } | { [k: string]: string },
): number | undefined {
  // @skjs-expect-error Invalid return type
  return x.a;
}

function unionFieldLeftIdxRightOk(
  x: { a: number } | { [k: string]: string },
): number | string | undefined {
  return x.a;
}

///////////////////////////////////////////////////////////////////////////////
// Test 25: Union — number index does NOT affect string-keyed fields
///////////////////////////////////////////////////////////////////////////////

function unionNumIdxNoEffect(
  x: { [k: number]: number } | { b: string },
): string | undefined {
  return x.b;
}

///////////////////////////////////////////////////////////////////////////////
// Test 26: Union — multiple fields with string index on other side
///////////////////////////////////////////////////////////////////////////////

function unionMultiFieldsVsIdx(
  x: { [k: string]: number } | { a: string; b: boolean },
): void {
  const v1: string | number | undefined = x.a;
  const v2: boolean | number | undefined = x.b;
}

///////////////////////////////////////////////////////////////////////////////
// Test 27: Union — number index widens numeric field name
///////////////////////////////////////////////////////////////////////////////

// x["0"]: left has number index (number), right has field "0" (string)
// Result should be string | number | undefined
function unionNumIdxNumFieldNarrow(
  x: { [k: number]: number } | { "0": string },
): string | undefined {
  // TODO: x["0"] should be string | number | undefined
  return x["0"];
}

function unionNumIdxNumFieldOk(
  x: { [k: number]: number } | { "0": string },
): string | number | undefined {
  return x["0"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 28: Union — number index does NOT widen non-numeric field name
///////////////////////////////////////////////////////////////////////////////

function unionNumIdxNonNumField(
  x: { [k: number]: number } | { a: string },
): string | undefined {
  return x.a;
}
