// Test partial support for the TypeScript `as` operator.
//
// SKJS accepts `e as T` only when the inferred type of `e` is a subtype of
// `T` (a sound upcast). All other shapes — downcasts, sideways casts,
// boundary casts from `unknown`, branded nominal types — are flagged but
// typechecking continues with the target type `T` so the user gets a single
// clear error per unsound cast instead of cascading failures.

///////////////////////////////////////////////////////////////////////////////
// Sound upcasts (accepted, no error)
///////////////////////////////////////////////////////////////////////////////

// Literal widened to its base primitive
function testLiteralToPrimitive(): void {
  const s: string = "foo" as string;
}

// Subclass-ish object widened to a supertype shape
type Animal = { name: string };
type Dog = { name: string; breed: string };
function testObjectUpcast(d: Dog): Animal {
  return d as Animal;
}

// Identity cast after narrowing: x is already `string` in the else branch
function testIdentityAfterNarrowing(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else {
    return (x as string).length;
  }
}

// Widening an array literal from ("a"|"b")[] to string[]
function testArrayLiteralWidening(): string[] {
  return ["a", "b"] as string[];
}

///////////////////////////////////////////////////////////////////////////////
// Unsound casts (error reported, but typing continues with the target type)
///////////////////////////////////////////////////////////////////////////////

// Downcast from `unknown`: unknown is NOT a subtype of number
function testDowncastFromUnknown(u: unknown): void {
  // @skjs-expect-error Unsound 'as' cast
  const n: number = u as number;
  // Typing continues: `n` is `number`, so arithmetic works
  const doubled: number = n * 2;
}

// Sideways primitive cast: number and string are unrelated
function testSidewaysPrimitive(): void {
  // @skjs-expect-error Unsound 'as' cast
  const s: string = 42 as string;
  // Typing continues: `s` is `string`, so `.length` works
  const len: number = s.length;
}

// Union not fully covered by the target type
function testUnionNotSubtype(x: number[] | { a: number }): number[] {
  // @skjs-expect-error Unsound 'as' cast
  return x as number[];
}

// Double-cast escape hatch: first half is sound (number <: unknown), second
// half is unsound (unknown </: string). Only the second `as` is flagged.
function testDoubleCastEscape(): void {
  // @skjs-expect-error Unsound 'as' cast
  const s: string = 1 as unknown as string;
  const len: number = s.length;
}
