// Regression tests for silent type-representation approximations (#76):
//   1. `keyof unknown`, `keyof never`, `keyof (A | B)`, and `keyof` on string
//      index signatures compute exact contravariant key sets instead of
//      over-approximating.
//   2. Materialized function intersection `F1 & F2` on incomparable signatures
//      preserves both overload signatures instead of silently collapsing to
//      `never` in TypeReadContext::funsInter.

///////////////////////////////////////////////////////////////////////////////
// Part 1: keyof on unknown, never, and unions
///////////////////////////////////////////////////////////////////////////////

type KUnknown = keyof unknown;
type KNever = keyof never;
type KUnionObj = keyof ({ a: number; b: string } | { a: number; c: boolean });
type KDisjointObj = keyof ({ a: number } | { b: string });
type KObjNull = keyof ({ a: number } | null);
type KObjUndef = keyof ({ a: number } | undefined);
type KObjStrIdx = keyof ({ a: number } | { [k: string]: number });
type KStrIdx = keyof { [k: string]: number };
type KStrNumIdxUnion = keyof (
  | { [k: string]: number }
  | { [k: number]: number }
);

function testKeyofUnknown(k: KUnknown): void {
  // keyof unknown is `never`.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const s: KUnknown = "anything";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: KUnknown = 42;
  const nev: never = k;
}

function testKeyofNever(): void {
  // keyof never is `string | number | symbol`.
  const s: KNever = "a";
  const n: KNever = 42;
  const sym: KNever = Symbol();
}

function testKeyofUnion(
  u: KUnionObj,
  d: KDisjointObj,
  kn: KObjNull,
  ku: KObjUndef,
  ks: KObjStrIdx,
): void {
  // Common key "a" is valid in KUnionObj and KObjStrIdx.
  const ok1: KUnionObj = "a";
  const ok2: KObjStrIdx = "a";

  // keyof (A | B) = (keyof A) & (keyof B).
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badB: KUnionObj = "b";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badC: KUnionObj = "c";
  const onlyA: "a" = u;

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badDisjoint: KDisjointObj = "a";
  const emptyDisjoint: never = d;

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badNull: KObjNull = "a";
  const emptyNull: never = kn;

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badUndef: KObjUndef = "a";
  const emptyUndef: never = ku;

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badStrIdx: KObjStrIdx = "other";
  const onlyAStrIdx: "a" = ks;
}

function testKeyofStringIndex(k: KStrNumIdxUnion): void {
  // keyof { [k: string]: number } is `string | number` (JS coerces numeric keys).
  const numKey: KStrIdx = 42;
  // keyof ({ [k: string]: number } | { [k: number]: number }) is `number`.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badStr: KStrNumIdxUnion = "abc";
  const onlyNum: number = k;
}

///////////////////////////////////////////////////////////////////////////////
// Part 2: Materialized function intersection `F1 & F2`
///////////////////////////////////////////////////////////////////////////////

type F1 = (x: number) => string;
type F2 = (x: string) => boolean;
type FI = F1 & F2;

declare const fi: FI;

function testNoLaunderFunctionIntersection(): number {
  // FI is an overloaded callable, NOT `never`, so it cannot be returned as `number`.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return fi;
}

type ObjFI = { f: F1 } & { f: F2 };
declare const ofi: ObjFI;

function testNoLaunderPropertyFunctionIntersection(): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return ofi.f;
}

type Ctor1 = new (x: number) => { a: number };
type Ctor2 = new (x: string) => { b: string };
type CtorI = Ctor1 & Ctor2;
declare const ct: CtorI;

function testNoLaunderConstructIntersection(): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return ct;
}

declare function ovl(x: number): string;
declare function ovl(x: string): boolean;

function testAssignFunctionIntersection(): void {
  const g: FI = ovl;
}

function testCallFunctionIntersection1(): string {
  return fi(1);
}

function testCallFunctionIntersection2(): boolean {
  return fi("hi");
}

function testForOfIntersectedReadonlyArrays(
  xs: readonly number[] & readonly unknown[],
): number {
  for (const x of xs) {
    return x;
  }
  return 0;
}
