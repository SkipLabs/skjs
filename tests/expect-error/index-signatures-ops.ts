///////////////////////////////////////////////////////////////////////////////
// Test 1: Union of indexed types
///////////////////////////////////////////////////////////////////////////////

interface StrIdx {
  [key: string]: number;
}
interface StrIdxStr {
  [key: string]: string;
}

type StrIdxUnion = StrIdx | StrIdxStr;

function testUnionAccess(x: StrIdxUnion): number | string | undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 2: Intersection of indexed types
///////////////////////////////////////////////////////////////////////////////

type StrIdxInter = StrIdx & StrIdxStr;

// number & string = never, so access gives never | undefined = undefined
function testInterAccess(x: StrIdxInter): undefined {
  return x["key"];
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: Union of indexed + non-indexed
///////////////////////////////////////////////////////////////////////////////

interface HasName {
  name: string;
}

type MixedUnion = StrIdx | HasName;

// On StrIdx: x.name gives number | undefined; on HasName: string
// Union should give string | number | undefined
function testMixedUnionField(x: MixedUnion): string | number | undefined {
  return x.name;
}

///////////////////////////////////////////////////////////////////////////////
// Test 4: Intersection of indexed + normal fields
///////////////////////////////////////////////////////////////////////////////

type MixedInter = StrIdx & HasName;

function testMixedInterIndex(x: MixedInter): number | undefined {
  return x["key"];
}

function testMixedInterField(x: MixedInter): string {
  return x.name;
}

///////////////////////////////////////////////////////////////////////////////
// Test 5: Assignability with unions containing indexed types
///////////////////////////////////////////////////////////////////////////////

function assignStrIdxToUnion(s: StrIdx): StrIdxUnion {
  return s;
}

function assignStrIdxStrToUnion(s: StrIdxStr): StrIdxUnion {
  return s;
}

///////////////////////////////////////////////////////////////////////////////
// Test 6: Dual-index types (string + number)
///////////////////////////////////////////////////////////////////////////////

interface DualIdx {
  [key: string]: number | string;
  [key: number]: number;
}

function testDualIdxString(x: DualIdx): number | string | undefined {
  return x["key"];
}

function testDualIdxNumber(x: DualIdx): number | undefined {
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 7: Cross-kind union
///////////////////////////////////////////////////////////////////////////////

interface NumIdx {
  [key: number]: number;
}

type StrNumUnion = StrIdx | NumIdx;

// TS: Property '0' does not exist on type 'StrNumUnion'
// Union means access must work on BOTH sides; NumIdx has no string index
// TODO: x[0] on StrNumUnion (TS errors, SKJS allows since StrIdx has string index covering number)
function testCrossKindUnionNum(x: StrNumUnion): number | undefined {
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 8: Cross-kind intersection
///////////////////////////////////////////////////////////////////////////////

type StrNumInter = StrIdx & NumIdx;

// Intersection: string index has number, number index also has number
function testCrossKindInterStr(x: StrNumInter): number | undefined {
  return x["key"];
}

function testCrossKindInterNum(x: StrNumInter): number | undefined {
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Test 9: String-indexed assignable to number-indexed (string covers number)
///////////////////////////////////////////////////////////////////////////////

function strIdxToNumIdx(s: StrIdx): NumIdx {
  return s;
}

// Number-indexed NOT assignable to string-indexed
function numIdxToStrIdx(n: NumIdx): StrIdx {
  // @skjs-expect-error Invalid return type
  return n;
}

///////////////////////////////////////////////////////////////////////////////
// Test 10: Dual-index assignability
///////////////////////////////////////////////////////////////////////////////

function dualToStrIdx(d: DualIdx): StrIdxUnion {
  // @skjs-expect-error Invalid return type
  return d;
}

function dualToNumIdx(d: DualIdx): NumIdx {
  return d;
}
