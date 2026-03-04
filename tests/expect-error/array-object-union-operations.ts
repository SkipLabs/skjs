///////////////////////////////////////////////////////////////////////////////
// Comprehensive tests for operations on Array<T> | Object union types
// Tests that the disjoint union (O&¬a | A&a) correctly handles various operations
//
// NOTE: This file is a work in progress and contains many test cases that expose
// interesting behaviors of the TObject disjoint union implementation.
// Many edge cases still need proper error annotations or fixes in the type system.
///////////////////////////////////////////////////////////////////////////////

type Obj = {
  name: string;
  value: number;
};

type ObjWithLength = {
  name: string;
  length: number;
};

///////////////////////////////////////////////////////////////////////////////
// Property access on unions
///////////////////////////////////////////////////////////////////////////////

// Accessing common property that exists in both branches
function testCommonProperty(x: Array<number> | ObjWithLength): number {
  // length exists in both Array and ObjWithLength
  // Both branches have length — works in TS too
  return x.length;
}

// Accessing array-only property
function testArrayOnlyProperty(x: Array<number> | Obj): number {
  // @skjs-expect-error Invalid index key
  // @skjs-expect-error Invalid return type
  return x.length;
}

// Accessing object-only property
function testObjectOnlyProperty(x: Array<number> | Obj): string {
  // @skjs-expect-error Invalid index key
  // @skjs-expect-error Invalid return type
  return x.name;
}

///////////////////////////////////////////////////////////////////////////////
// Method calls on unions
///////////////////////////////////////////////////////////////////////////////

// Calling array method on union
function testArrayMethodOnUnion(x: Array<number> | Obj): Array<number> {
  // @skjs-expect-error Invalid call
  // @skjs-expect-error Invalid index key
  return x.map((n) => n * 2);
}

// Calling push on union
function testPushOnUnion(x: Array<number> | Obj): void {
  // @skjs-expect-error Invalid call
  // @skjs-expect-error Invalid index key
  x.push(42);
}

///////////////////////////////////////////////////////////////////////////////
// Index access on unions
///////////////////////////////////////////////////////////////////////////////

// Numeric index on array | object union
function testNumericIndexOnUnion(x: Array<string> | Obj): string | undefined {
  // FIXME: TS errors here (index 0 doesn't exist on string[] | Obj), SKJS allows it
  return x[0];
}

// String index on array | object union
function testStringIndexOnUnion(x: Array<number> | Obj): string | undefined {
  // @skjs-expect-error Invalid index key
  // @skjs-expect-error Invalid return type
  return x["name"];
}

///////////////////////////////////////////////////////////////////////////////
// Assignment to union types
///////////////////////////////////////////////////////////////////////////////

// Assigning array to union variable
function testAssignArrayToUnion(): Array<number> | Obj {
  const arr: Array<number> = [1, 2, 3];
  // Array<number> is assignable to Array<number> | Obj — matches TS
  return arr;
}

// Assigning object to union variable
function testAssignObjectToUnion(): Array<number> | Obj {
  const obj: Obj = { name: "test", value: 42 };
  // Obj is assignable to Array<number> | Obj — matches TS
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Operations that work on both branches
///////////////////////////////////////////////////////////////////////////////

// typeof on union (should work, returns "object" for both)
function testTypeofOnUnion(x: Array<number> | Obj): string {
  return typeof x;
}

// Equality comparison
function testEqualityOnUnion(
  x: Array<number> | Obj,
  y: Array<number> | Obj,
): boolean {
  return x === y;
}

///////////////////////////////////////////////////////////////////////////////
// Intersection of array | object unions
///////////////////////////////////////////////////////////////////////////////

type Obj2 = {
  name: string;
  id: number;
};

// Intersection should work on object branches
function testIntersectionObjects(
  z: (Array<number> | Obj) & (Array<string> | Obj2),
): Obj & Obj2 {
  // This tests that intersection of (Array<number> | Obj) & (Array<string> | Obj2)
  // should give us (never | {name: string, value: number, id: number})
  // @skjs-expect-error Invalid return type
  return z;
}

///////////////////////////////////////////////////////////////////////////////
// Union with multiple object types
///////////////////////////////////////////////////////////////////////////////

type Obj3 = {
  label: string;
};

function testMultipleObjectsGetName(x: Array<number> | Obj | Obj3): string {
  // Can't access any specific property without refinement
  // @skjs-expect-error Invalid index key
  // @skjs-expect-error Invalid return type
  return x.name;
}

function testMultipleObjectsGetLabel(x: Array<number> | Obj | Obj3): string {
  // @skjs-expect-error Invalid index key
  // @skjs-expect-error Invalid return type
  return x.label;
}

///////////////////////////////////////////////////////////////////////////////
// Spread operations
///////////////////////////////////////////////////////////////////////////////

// Spreading array from union
function testSpreadArrayFromUnion(x: Array<number> | Obj): Array<number> {
  // @skjs-expect-error Invalid iterable type for for-of loop
  // @skjs-expect-error Invalid return type
  return [...x];
}

///////////////////////////////////////////////////////////////////////////////
// For-of loops
///////////////////////////////////////////////////////////////////////////////

// Iterating over union
function testForOfOnUnion(x: Array<number> | Obj): void {
  // @skjs-expect-error Invalid iterable type for for-of loop
  for (const item of x) {
    console.log(item);
  }
}

///////////////////////////////////////////////////////////////////////////////
// Array destructuring
///////////////////////////////////////////////////////////////////////////////

// Destructuring union
function testDestructuringUnion(x: Array<number> | Obj): void {
  // @skjs-expect-error Invalid tuple pattern
  const [first, second] = x;
}

///////////////////////////////////////////////////////////////////////////////
// Subtyping with unions
///////////////////////////////////////////////////////////////////////////////

// Array<number> should be subtype of Array<number> | Obj
function testArraySubtypeOfUnion(arr: Array<number>): Array<number> | Obj {
  // Array<number> is subtype of Array<number> | Obj — matches TS
  return arr;
}

// Obj should be subtype of Array<number> | Obj
function testObjectSubtypeOfUnion(obj: Obj): Array<number> | Obj {
  // Obj is subtype of Array<number> | Obj — matches TS
  return obj;
}

// Union should not be subtype of just Array
function testUnionNotSubtypeOfArray(x: Array<number> | Obj): Array<number> {
  // @skjs-expect-error Invalid return type
  return x;
}

// Union should not be subtype of just Object
function testUnionNotSubtypeOfObject(x: Array<number> | Obj): Obj {
  // @skjs-expect-error Invalid return type
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Narrowing with Array.isArray
///////////////////////////////////////////////////////////////////////////////

// After Array.isArray, should be narrowed to array
function testNarrowToArray(x: Array<number> | Obj): Array<unknown> {
  if (Array.isArray(x)) {
    return x;
  }
  return [];
}

// After negative Array.isArray, should be narrowed to object
function testNarrowToObject(x: Array<number> | Obj): Obj {
  if (!Array.isArray(x)) {
    // @skjs-expect-error Invalid return type
    return x;
  }
  return { name: "", value: 0 };
}

///////////////////////////////////////////////////////////////////////////////
// Complex nested unions
///////////////////////////////////////////////////////////////////////////////

// Union of unions
function testNestedUnionsGetFirst(
  x: (Array<number> | Obj) | (Array<string> | Obj3),
): number | string {
  // Should require refinement to access anything
  // @skjs-expect-error Invalid return type
  return x[0];
}

///////////////////////////////////////////////////////////////////////////////
// Generic functions with array | object constraints
///////////////////////////////////////////////////////////////////////////////

function testGenericArrayOrObject<T extends Array<number> | Obj>(x: T): T {
  return x;
}
// Same shape as above, only binder name differs (S instead of T).
function testGenericArrayOrObjectS<S extends Array<number> | Obj>(x: S): S {
  return x;
}

// Using the generic function
function testUseGenericArrayOrObject(): void {
  const arr: Array<number> = [1, 2, 3];
  const result1 = testGenericArrayOrObject(arr);
  const result1S = testGenericArrayOrObjectS(arr);

  const obj: Obj = { name: "test", value: 42 };
  // Obj satisfies constraint Array<number> | Obj — matches TS
  const result2 = testGenericArrayOrObject(obj);
  const result2S = testGenericArrayOrObjectS(obj);
}

///////////////////////////////////////////////////////////////////////////////
// Array literal vs object literal assignment
///////////////////////////////////////////////////////////////////////////////

function testLiteralAssignment(): void {
  // Array literal to union - works!
  const x: Array<number> | Obj = [1, 2, 3];

  // Object literal to union - works!
  const y: Array<number> | Obj = { name: "test", value: 42 };
}

///////////////////////////////////////////////////////////////////////////////
// Intersection with other types
///////////////////////////////////////////////////////////////////////////////

// Intersection with string (should be never)
function testIntersectionWithString(x: (Array<number> | Obj) & string): never {
  return x;
}

// Intersection with object type
function testIntersectionWithObjectType(
  x: (Array<number> | Obj) & { extra: boolean },
): boolean {
  // Intersection distributes: extra is accessible — matches TS
  return x.extra;
}
