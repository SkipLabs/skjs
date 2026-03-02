// Intersection and union of readonly/non-readonly fields.
//
// Intersection: {readonly x: T} & {x: T} makes x mutable
//   (set = union(bottom, T) = T)
// Union: {readonly x: T} | {x: U} makes x readonly
//   (set = inter(bottom, U) = bottom)

// ============================================================
// 1. Intersection: readonly + mutable → mutable
// ============================================================

type ReadonlyX = { readonly x: string };
type MutableX = { x: string };
type InterRM = ReadonlyX & MutableX;

// Intersection makes field writable (mutable interface available)
function writeIntersection(b: InterRM): void {
  b.x = "hello";
}

function readIntersection(b: InterRM): string {
  return b.x;
}

// ============================================================
// 2. Union: readonly + mutable → readonly
// ============================================================

type ReadonlyY = { readonly y: string };
type MutableY = { y: number };
type UnionRM = ReadonlyY | MutableY;

function readUnion(u: UnionRM): string | number {
  return u.y;
}

// Union makes field readonly (one branch is readonly)
function writeUnion(u: UnionRM): void {
  // @skjs-expect-error Invalid assignment
  u.y = 42;
}

// ============================================================
// 3. Subtyping: readonly struct passed where intersection expected
// ============================================================

function takesInter(b: InterRM): void {
  b.x = "modified";
}

function passReadonlyToInter(): void {
  const ro: ReadonlyX = { x: "immutable" };
  // Readonly is not assignable to intersection (which requires mutable)
  // @skjs-expect-error Invalid call
  takesInter(ro);
}
