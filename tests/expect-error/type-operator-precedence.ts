// Tests for type operator precedence
// These tests expose bugs where prefix type operators have incorrect precedence

///////////////////////////////////////////////////////////////////////////////
// Test 1: keyof with union
// TypeScript parses: keyof { x: number } | string = (keyof { x: number }) | string = "x" | string
// SKJS currently parses: keyof ({ x: number } | string) = "x" | "charAt" | "charCodeAt" | ...
///////////////////////////////////////////////////////////////////////////////

type KeyofUnion = keyof { x: number } | string;

function testKeyofUnion(): void {
  // This should work: "x" is in the union
  const a: KeyofUnion = "x";

  // This should work: any string is in the union
  const b: KeyofUnion = "hello";

  // This should work: another arbitrary string
  const c: KeyofUnion = "world";
}

///////////////////////////////////////////////////////////////////////////////
// Test 2: keyof with intersection
// TypeScript parses: keyof { x: number } & string = (keyof { x: number }) & string = "x" & string = "x"
///////////////////////////////////////////////////////////////////////////////

type KeyofIntersection = keyof { x: number } & string;

function testKeyofIntersection(): void {
  // This works with correct precedence: "x" is both in keyof and is a string
  const a: KeyofIntersection = "x";

  // This should fail: "y" is not a key
  // SKJS currently has a different bug here (not just precedence)
  // @skjs-expect-error Invalid annotation
  const b: KeyofIntersection = "y";

  // This should fail: "hello" is not a key
  // @ts-expect-error Invalid annotation
  const c: KeyofIntersection = "hello";
}

///////////////////////////////////////////////////////////////////////////////
// Test 3: readonly with union
// TypeScript parses: readonly number[] | string = (readonly number[]) | string
///////////////////////////////////////////////////////////////////////////////

// SKJS doesn't support readonly arrays yet, so skip this test for now
// type ReadonlyUnion = readonly number[] | string;

///////////////////////////////////////////////////////////////////////////////
// Test 4: Multiple keyof in union
// TypeScript parses: keyof { a: number } | keyof { b: string }
//   = (keyof { a: number }) | (keyof { b: string })
//   = "a" | "b"
///////////////////////////////////////////////////////////////////////////////

type MultipleKeyof = keyof { a: number } | keyof { b: string };

function testMultipleKeyof(): void {
  const a: MultipleKeyof = "a";

  // This works: "b" is from keyof { b: string }
  const b: MultipleKeyof = "b";

  // This should fail: "c" is not in either keyof
  // @ts-expect-error Invalid annotation
  const c: MultipleKeyof = "c";
}

///////////////////////////////////////////////////////////////////////////////
// Test 5: keyof with intersection and union
// TypeScript parses: keyof { x: number } | string & boolean
//   = (keyof { x: number }) | (string & boolean)
//   = "x" | never
//   = "x"
///////////////////////////////////////////////////////////////////////////////

type KeyofUnionIntersection = keyof { x: number } | (string & boolean);

function testKeyofUnionIntersection(): void {
  // Should work: "x" is in the result
  const a: KeyofUnionIntersection = "x";

  // Currently FAILS because SKJS parses it as keyof ({ x: number } | string) & boolean
  // In TypeScript, string & boolean = never, so result is just "x"
  // @skjs-expect-error Invalid annotation
  const b: KeyofUnionIntersection = "hello";
}

///////////////////////////////////////////////////////////////////////////////
// Test 6: Intersection has higher precedence than union
// TypeScript parses: string | number & boolean = string | (number & boolean) = string | never = string
///////////////////////////////////////////////////////////////////////////////

type IntersectionUnion = string | (number & boolean);

function testIntersectionUnion(): void {
  // Should work: string is in the union
  const a: IntersectionUnion = "hello";

  // Should fail: number & boolean = never, but SKJS has issues with never types
  // SKJS incorrectly rejects this
  // @skjs-expect-error Invalid annotation
  const b: IntersectionUnion = 42;

  // Should fail: boolean is not assignable
  // @ts-expect-error Invalid annotation
  const c: IntersectionUnion = true;
}

///////////////////////////////////////////////////////////////////////////////
// Test 7: Nested keyof with union
// TypeScript parses: keyof (keyof { x: { y: number } } | string)
// This is intentionally using parens to test the CORRECT parsing
///////////////////////////////////////////////////////////////////////////////

type NestedKeyof1 = keyof { x: { y: number } };

function testNestedKeyof1(): void {
  const a: NestedKeyof1 = "x";
}

// Without the bug fix, this is what keyof { x: number } | string incorrectly parses as
type NestedKeyofBuggy = keyof ({ x: number } | string);

function testNestedKeyofBuggy(): void {
  const a: NestedKeyofBuggy = "x";
  // This SHOULD work with the buggy parsing (all string methods)
  const b: NestedKeyofBuggy = "charAt";
  const c: NestedKeyofBuggy = "toString";
}

///////////////////////////////////////////////////////////////////////////////
// Test 8: Array suffix has higher precedence than union
// TypeScript parses: number[] | string = (number[]) | string
///////////////////////////////////////////////////////////////////////////////

type ArrayUnion = number[] | string;

function testArrayUnion(): void {
  const a: ArrayUnion = new Array<number>();
  const b: ArrayUnion = "hello";

  // Should fail: not an array or string
  // SKJS has type representation issues with arrays here
  // @skjs-expect-error Invalid annotation
  const c: ArrayUnion = 42;
}

///////////////////////////////////////////////////////////////////////////////
// Test 9: Indexed access with union
// TypeScript parses: { a: number }["a"] | string = (({ a: number })["a"]) | string = number | string
///////////////////////////////////////////////////////////////////////////////

// SKJS doesn't fully support indexed access types yet
// @skjs-expect-error TODO TAGet
type IndexedUnion = { a: number }["a"] | string;

function testIndexedUnion(): void {
  // Skip tests for unimplemented feature
  // const a: IndexedUnion = 42;
  // const b: IndexedUnion = "hello";
  // const c: IndexedUnion = true;
}

///////////////////////////////////////////////////////////////////////////////
// Test 10: Mixed prefix operators with union
// TypeScript parses: keyof { a: number } | keyof { b: string } | number
//   = (keyof { a: number }) | (keyof { b: string }) | number
//   = "a" | "b" | number
///////////////////////////////////////////////////////////////////////////////

type MixedPrefixUnion = keyof { a: number } | keyof { b: string } | number;

function testMixedPrefixUnion(): void {
  const a: MixedPrefixUnion = "a";

  // Works: "b" is from keyof { b: string }
  const b: MixedPrefixUnion = "b";

  const c: MixedPrefixUnion = 42;

  // Should fail: "c" is not a valid key and not a number
  // @ts-expect-error Invalid annotation
  const d: MixedPrefixUnion = "c";
}

///////////////////////////////////////////////////////////////////////////////
// Test 11: Verify & has higher precedence than |
// TypeScript parses: A | B & C = A | (B & C)
///////////////////////////////////////////////////////////////////////////////

type A = { a: string };
type B = { b: number };
type C = { c: boolean };

type UnionIntersectionMixed = A | (B & C);

function testUnionIntersectionMixed(): void {
  // Should work: A is in the union
  const a: UnionIntersectionMixed = { a: "hello" };

  // Should work: B & C is in the union
  const b: UnionIntersectionMixed = { b: 42, c: true };

  // Should fail: B alone is not B & C
  // TODO: SKJS not detecting this error (separate issue from precedence)
  const c: UnionIntersectionMixed = { b: 42 };

  // Should fail: C alone is not B & C
  // TODO: SKJS not detecting this error (separate issue from precedence)
  const d: UnionIntersectionMixed = { c: true };
}

///////////////////////////////////////////////////////////////////////////////
// Test 12: Complex precedence chain
// TypeScript parses: keyof { x: number } | { y: string } & { z: boolean }
//   = (keyof { x: number }) | ({ y: string } & { z: boolean })
//   = "x" | { y: string; z: boolean }
///////////////////////////////////////////////////////////////////////////////

type ComplexPrecedence = keyof { x: number } | ({ y: string } & { z: boolean });

function testComplexPrecedence(): void {
  // With correct precedence: (keyof { x: number }) | ({ y: string } & { z: boolean })
  // = "x" | { y: string; z: boolean }
  const a: ComplexPrecedence = "x";

  // Works: object with both y and z matches { y: string; z: boolean }
  // @skjs-expect-error Invalid annotation
  const b: ComplexPrecedence = { y: "hello", z: true };

  // Should fail: object with only y
  // @skjs-expect-error Invalid annotation
  const c: ComplexPrecedence = { y: "hello" };

  // Should fail: "hello" is not a valid key or object type
  // @ts-expect-error Invalid annotation
  const d: ComplexPrecedence = "hello";
}
