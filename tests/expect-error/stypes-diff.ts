// Test: Type inference with union-typed parameters.
//
// When a generic function has a parameter type like `"literal" | T`, the
// type checker must correctly infer T from arguments that don't match the
// literal.

// Argument matches explicit branch of union
// When the argument type is covered by a non-T branch, T is unconstrained.

function takeStringOrT<T>(x: string | T): void {}

function testArgumentCovered(): void {
  // string matches the string branch, so T is unconstrained
  const s: string = "hello";
  takeStringOrT(s);
}

// Inferring T from a different literal

function takeFooOrT<T>(x: "foo" | T): void {}

function testDifferentLiteral(): void {
  // "foo" matches the literal branch directly
  takeFooOrT("foo" as const);

  // Explicit type argument works
  takeFooOrT<"bar">("bar" as const);

  // "bar" doesn't match "foo", so T is inferred to include "bar"
  // @skjs-expect-error Invalid call
  takeFooOrT("bar" as const);
}

// Multiple type parameters in unions
function takeTwoUnions<T, U>(a: "foo" | T, b: "bar" | U): void {}

function testMultipleTypeParams(): void {
  // @skjs-expect-error Invalid call
  takeTwoUnions("x" as const, "y" as const);
}

// Object types in unions

type ObjA = { a: number };
type ObjB = { a: string };

function takeObjAOrT<T>(x: ObjA | T): void {}

function testObjectInUnion(): void {
  const objB: ObjB = { a: "hello" };
  // ObjB doesn't match ObjA, so T is inferred to include ObjB
  takeObjAOrT(objB);
}

// Tuple types in unions

function takeTupleOrT<T>(x: [number, string] | T): void {}

function testTupleInUnion(): void {
  const t: [string, number] = ["a", 1];
  // Different tuple structure, so T is inferred
  // @skjs-expect-error Invalid call
  takeTupleOrT(t);
}

// Same-shape objects in unions

type SameShape = { x: number };

function takeSameShapeOrT<T>(x: SameShape | T): void {}

function testSameShapeObject(): void {
  const obj: SameShape = { x: 42 };
  // Object matches the first branch, T may or may not be constrained
  takeSameShapeOrT(obj);
}

// Nullish types in unions

function takeUndefinedOrT<T>(x: undefined | T): void {}

function testNullishInUnion(): void {
  // undefined matches the undefined branch exactly, so T is unconstrained
  takeUndefinedOrT(undefined);
}

// Literal argument with full type in union (literal - full = bottom)

function testLiteralVsFull(): void {
  // "foo" is a subtype of string, so it matches the string branch
  // T is unconstrained
  takeStringOrT("foo" as const);
}

// Full type argument with literal in union (full - literal = full)

function takeLiteralOrT<T>(x: "foo" | T): void {}

function testFullVsLiteral(): void {
  // string is not covered by "foo", so T must include string
  const s: string = "hello";
  // @skjs-expect-error Invalid call
  takeLiteralOrT(s);
}

// Argument type has component not in parameter union (left only case)

function takeStringOrNumberOrT<T>(x: string | number | T): void {}

function testLeftOnly(): void {
  // boolean is not covered by string or number, so T must include boolean
  const b: boolean = true;
  takeStringOrNumberOrT(b);
}

// Promise types in unions

function takePromiseOrT<T>(x: Promise<number> | T): void {}

function testPromiseInUnion(p: Promise<string>): void {
  // Promise<string> doesn't match Promise<number>, so T is inferred
  // @skjs-expect-error Invalid call
  takePromiseOrT(p);
}

// Discriminated unions (algebraic types)

type Result<T> = { tag: "ok"; value: T } | { tag: "error"; message: string };

function takeResultOrT<T>(x: Result<number> | T): void {}

function testAlgebraicInUnion(): void {
  // Result<string> doesn't match Result<number>, so T is inferred
  const r: Result<string> = { tag: "ok", value: "hello" };
  takeResultOrT(r);
}

// Practical example: option-like pattern

function unwrapOr<T>(x: T | undefined, defaultValue: T): T {
  return x ?? defaultValue;
}

function testOptionPattern(): void {
  // T is inferred from both arguments
  const result = unwrapOr("hello", "default");
  const check: "hello" | "default" = result;
}
