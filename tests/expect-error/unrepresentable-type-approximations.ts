// Pinning tests for silent type-representation approximations (#76):
//   1. `keyof unknown`, `keyof never`, and `keyof (A | B)` (union of types)
//      currently over-approximate `keyof` instead of intersecting member keys /
//      computing exact contravariant bounds.
//   2. Materialized function intersection `F1 & F2` on incomparable signatures
//      currently collapses to `never` in TypeReadContext::funsInter, allowing
//      values of inhabited overloaded intersections to be laundered to any type.

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

function pinKeyofUnknown(k: KUnknown): void {
  // BUG (#76): keyof unknown currently over-approximates as `number | string`
  // instead of `never`, so arbitrary strings/numbers are accepted and `k` is
  // not assignable to `never`.
  const s: KUnknown = "anything";
  const n: KUnknown = 42;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const nev: never = k;
}

function pinKeyofNever(): void {
  // BUG (#76): keyof never currently evaluates to `never` instead of
  // `string | number | symbol`.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const s: KNever = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: KNever = 42;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const sym: KNever = Symbol();
}

function pinKeyofUnion(
  u: KUnionObj,
  d: KDisjointObj,
  kn: KObjNull,
  ku: KObjUndef,
  ks: KObjStrIdx,
): void {
  // Common key "a" is valid in KUnionObj and KObjStrIdx.
  const ok1: KUnionObj = "a";
  const ok2: KObjStrIdx = "a";

  // BUG (#76): keyof (A | B) currently unions member keys instead of
  // intersecting them, accepting non-common keys and rejecting narrowing to
  // the common key set.
  const badB: KUnionObj = "b";
  const badC: KUnionObj = "c";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const onlyA: "a" = u;

  const badDisjoint: KDisjointObj = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const emptyDisjoint: never = d;

  const badNull: KObjNull = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const emptyNull: never = kn;

  const badUndef: KObjUndef = "a";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const emptyUndef: never = ku;

  const badStrIdx: KObjStrIdx = "other";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const onlyAStrIdx: "a" = ks;
}

function pinKeyofStringIndex(k: KStrNumIdxUnion): void {
  // BUG (#76): keyof { [k: string]: number } currently omits `number`
  // (JS coerces number keys to strings, so tsc evaluates it to `string | number`).
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const numKey: KStrIdx = 42;
  // BUG (#76): keyof ({ [k: string]: number } | { [k: number]: number })
  // currently unions to `string | number` instead of intersecting to `number`.
  const badStr: KStrNumIdxUnion = "abc";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const onlyNum: number = k;
}

///////////////////////////////////////////////////////////////////////////////
// Part 2: Materialized function intersection `F1 & F2`
///////////////////////////////////////////////////////////////////////////////

type F1 = (x: number) => string;
type F2 = (x: string) => boolean;
type FI = F1 & F2;

declare const fi: FI;

function pinLaunderFunctionIntersection(): number {
  // BUG (#76): FI collapses to `never` during type-read normalization, so an
  // inhabited overloaded function value is unsoundly assignable to `number`!
  return fi;
}

type ObjFI = { f: F1 } & { f: F2 };
declare const ofi: ObjFI;

function pinLaunderPropertyFunctionIntersection(): number {
  // BUG (#76): Same silent collapse inside intersected object properties.
  return ofi.f;
}

type Ctor1 = new (x: number) => { a: number };
type Ctor2 = new (x: string) => { b: string };
type CtorI = Ctor1 & Ctor2;
declare const ct: CtorI;

function pinLaunderConstructIntersection(): number {
  // BUG (#76): Same silent collapse for construct-signature intersections.
  return ct;
}

declare function ovl(x: number): string;
declare function ovl(x: string): boolean;

function pinAssignFunctionIntersection(): void {
  // BUG (#76): Because FI collapsed to `never`, an overloaded function cannot
  // be assigned to FI.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const g: FI = ovl;
}

function pinCallFunctionIntersection1(): string {
  // BUG (#76): Because FI collapsed to `never`, calling fi fails with
  // "This expression is not callable".
  // @skjs-expect-error This expression is not callable
  return fi(1);
}

function pinCallFunctionIntersection2(): boolean {
  // @skjs-expect-error This expression is not callable
  return fi("hi");
}
