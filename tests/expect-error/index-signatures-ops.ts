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
  // @skjs-expect-error Unbound field: name
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
