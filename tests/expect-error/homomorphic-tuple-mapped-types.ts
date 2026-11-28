///////////////////////////////////////////////////////////////////////////////
// Tests for tuple- and array-preserving homomorphic mapped types (#634 §1b),
// indexed access `T[K]` for literal keys, and `readonly` modifiers on mapped
// types.
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type Mutable<T> = { -readonly [P in keyof T]: T[P] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type ReadonlyMapped<T> = { readonly [P in keyof T]: T[P] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type PlusReadonlyMapped<T> = { +readonly [P in keyof T]: T[P] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type IdentityMapped<T> = { [P in keyof T]: T[P] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type BoxAll<T> = { [P in keyof T]: [T[P]] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type MutableBoxAll<T> = { -readonly [P in keyof T]: [T[P]] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type KeyedAll<T> = { [P in keyof T]: { key: P; val: T[P] } };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type RequiredMapped<T> = { [P in keyof T]-?: T[P] };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type OptionalMapped<T> = { [P in keyof T]?: T[P] };

///////////////////////////////////////////////////////////////////////////////
// 1. Mutable on readonly tuple -> mutable tuple of same arity
///////////////////////////////////////////////////////////////////////////////

type MutTuple = Mutable<readonly [number, string]>;

function mutTupleWorks(): MutTuple {
  const t: MutTuple = [1, "a"];
  t[0] = 2;
  t[1] = "b";
  return t;
}

function mutTupleWrongElem(): void {
  const t: MutTuple = [1, "a"];
  t[0] = "nope";
}

// Soundness: readonly tuple is NOT assignable to mutable tuple
function mutTupleRejectsReadonly(ro: readonly [number, string]): MutTuple {
  return ro;
}

// Soundness: mutable tuple is invariant in its element types (stricter than tsc)
function mutTupleRejectsNarrowMutable(narrow: [1, "a"]): MutTuple {
  return narrow;
}

///////////////////////////////////////////////////////////////////////////////
// 2. readonly / +readonly on mutable tuple -> readonly tuple
///////////////////////////////////////////////////////////////////////////////

type RoTuple = ReadonlyMapped<[number, string]>;

function roTupleAcceptsMutable(m: [number, string]): RoTuple {
  return m;
}

function roTupleForbidsWrite(t: RoTuple): void {
  t[0] = 2;
}

type PlusRoTuple = PlusReadonlyMapped<[number, string]>;

function plusRoTupleForbidsWrite(t: PlusRoTuple): void {
  t[0] = 2;
}

///////////////////////////////////////////////////////////////////////////////
// 3. Identity preserves readonly-ness
///////////////////////////////////////////////////////////////////////////////

type IdRo = IdentityMapped<readonly [number, string]>;

function idRoForbidsWrite(t: IdRo): void {
  t[0] = 2;
}

type IdMut = IdentityMapped<[number, string]>;

function idMutAllowsWrite(t: IdMut): void {
  t[0] = 2;
  t[1] = "ok";
}

///////////////////////////////////////////////////////////////////////////////
// 4. Value transform using T[P]
///////////////////////////////////////////////////////////////////////////////

type BoxedRo = BoxAll<readonly [number, string]>;

function boxedRoWorks(): BoxedRo {
  const b: BoxedRo = [[1], ["a"]];
  const n: number = b[0][0];
  const s: string = b[1][0];
  return [[n], [s]];
}

function boxedRoForbidsWrite(b: BoxedRo): void {
  b[0] = [2];
}

type BoxedMut = MutableBoxAll<readonly [number, string]>;

function boxedMutAllowsWrite(): BoxedMut {
  const b: BoxedMut = [[1], ["a"]];
  b[0] = [2];
  return b;
}

///////////////////////////////////////////////////////////////////////////////
// 5. Direct P reference in value type ("0"/"1" on tuple, number on array)
///////////////////////////////////////////////////////////////////////////////

type KeyedTup = KeyedAll<readonly [number, string]>;

function keyedTupWorks(): KeyedTup {
  return [
    { key: "0", val: 1 },
    { key: "1", val: "a" },
  ];
}

function keyedTupRejectsWrongIndex(): KeyedTup {
  return [
    { key: "1", val: 1 },
    { key: "1", val: "a" },
  ];
}

type KeyedArr = KeyedAll<readonly string[]>;

function keyedArrWorks(): KeyedArr {
  return [
    { key: 0, val: "a" },
    { key: 5, val: "b" },
  ];
}

function keyedArrRejectsStringKey(): KeyedArr {
  return [{ key: "0", val: "a" }];
}

///////////////////////////////////////////////////////////////////////////////
// 6. Array preservation (mutable / readonly / transform)
///////////////////////////////////////////////////////////////////////////////

type MutArr = Mutable<readonly number[]>;

function mutArrWorks(): MutArr {
  const a: MutArr = [1, 2];
  a[0] = 3;
  a.push(4);
  return a;
}

function mutArrRejectsReadonly(ro: readonly number[]): MutArr {
  return ro;
}

type RoArr = ReadonlyMapped<number[]>;

function roArrForbidsWrite(a: RoArr): void {
  a[0] = 3;
}

type BoxArr = BoxAll<readonly string[]>;

function boxArrWorks(): BoxArr {
  const a: BoxArr = [["a"], ["b"]];
  return a;
}

function boxArrForbidsWrite(a: BoxArr): void {
  a[0] = ["c"];
}

///////////////////////////////////////////////////////////////////////////////
// 7. Distribution over unions of tuples and arrays
///////////////////////////////////////////////////////////////////////////////

type DistTuples = BoxAll<
  readonly [number, string] | readonly [boolean, number]
>;

function distTuplesAcceptsBranch1(): DistTuples {
  return [[1], ["a"]];
}

function distTuplesAcceptsBranch2(): DistTuples {
  return [[true], [2]];
}

function distTuplesRejectsMixed(): DistTuples {
  return [[1], [2]];
}

type DistMixed = Mutable<readonly [number, string] | readonly boolean[]>;

function distMixedAcceptsTuple(): DistMixed {
  return [1, "a"];
}

function distMixedAcceptsArray(): DistMixed {
  return [true, false, true];
}

///////////////////////////////////////////////////////////////////////////////
// 8. Distribution over never
///////////////////////////////////////////////////////////////////////////////

type NeverMapped = Mutable<never>;

function neverMappedToNumber(x: NeverMapped): number {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// 9. Alias to tuple / nested homomorphic mapped types / generic function
///////////////////////////////////////////////////////////////////////////////

type Pair = readonly [number, string];
type MutPair = Mutable<Pair>;

function mutPairWorks(): MutPair {
  const p: MutPair = [1, "a"];
  p[0] = 2;
  return p;
}

type DoubleBox = BoxAll<BoxAll<readonly [number, string]>>;

function doubleBoxWorks(): DoubleBox {
  return [[[1]], [["a"]]];
}

function unfreezePair<A, B>(p: readonly [A, B]): Mutable<readonly [A, B]> {
  return [p[0], p[1]];
}

function useUnfreezePair(): [number, string] {
  const x: readonly [number, string] = [1, "a"];
  const y = unfreezePair(x);
  y[0] = 2;
  return y;
}

///////////////////////////////////////////////////////////////////////////////
// 10. Optional modifiers (-? on tuple, ? on array, ? on tuple rejected)
///////////////////////////////////////////////////////////////////////////////

type ReqRo = RequiredMapped<readonly [number, string]>;

function reqRoForbidsWrite(t: ReqRo): void {
  t[0] = 2;
}

type OptArr = OptionalMapped<number[]>;

function optArrWorks(): OptArr {
  const a: OptArr = [1, undefined, 2];
  return a;
}

// Optional tuple elements are not yet supported by SKJS
type OptTuple = OptionalMapped<readonly [number, string]>;

///////////////////////////////////////////////////////////////////////////////
// 11. Abstract T outside type-definition validation stays rejected
///////////////////////////////////////////////////////////////////////////////

function abstractHomomorphic<T extends readonly unknown[]>(
  x: T,
  // @skjs-expect-error keyof on an abstract type is not yet supported by SKJS; use a known object or array shape with explicit type parameters
): Mutable<T> {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// 12. Non-homomorphic readonly mapped object types (existing readonly bug)
///////////////////////////////////////////////////////////////////////////////

type RoMap = { readonly [P in "a" | "b"]: number };

function roMapForbidsWrite(m: RoMap): void {
  // Currently unsoundly accepted because createTFields drops readonly_ for FNIn.
  m.a = 2;
}

type PlusRoMap = { +readonly [P in "a" | "b"]: number };

function plusRoMapForbidsWrite(m: PlusRoMap): void {
  // Currently unsoundly accepted because createTFields drops readonly_ for FNIn.
  m.a = 2;
}

type RoStringMap = { readonly [P in string]: number };

function roStringMapForbidsWrite(m: RoStringMap): void {
  // Currently unsoundly accepted because createTFields drops readonly_ for FNIn.
  m["x"] = 2;
}

///////////////////////////////////////////////////////////////////////////////
// 13. Indexed access T[K] with literal keys & circularity
///////////////////////////////////////////////////////////////////////////////

// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type Pair0 = Pair[0];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type Pair1 = Pair["1"];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type PairLen = Pair["length"];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type Pair01 = Pair[0 | 1];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type PairOOB = Pair[2];

type Obj = { a: number; b?: string };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type ObjA = Obj["a"];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type ObjB = Obj["b"];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type ObjMissing = Obj["missing"];

// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type CircIdx = CircIdx["a"];
