// Pinning tests for:
// 1. Conflicting call/construct signatures inherited across multiple interface
//    `extends` bases (an earlier base shadows a later base with an incompatible
//    return type, making the combined interface inconsistent).
// 2. Shadowed (unreachable) intra-declaration overload signatures (an earlier
//    overload covers all arguments accepted by a later overload, so the later
//    signature can never be selected).

// ---------------------------------------------------------------------------
// 1. Conflicting `extends` call / construct signatures
// ---------------------------------------------------------------------------

interface CallBaseA {
  (x: string): number;
}
interface CallBaseB {
  (x: string): string;
}
// @skjs-expect-error Interface 'ConflictCallSub' cannot simultaneously extend 'CallBaseA' and 'CallBaseB': conflicting call signatures
interface ConflictCallSub extends CallBaseA, CallBaseB {}

interface NewBaseA {
  new (x: string): { a: number };
}
interface NewBaseB {
  new (x: string): { b: string };
}
// @skjs-expect-error Interface 'ConflictNewSub' cannot simultaneously extend 'NewBaseA' and 'NewBaseB': conflicting construct signatures
interface ConflictNewSub extends NewBaseA, NewBaseB {}

// Compatible refinement across extends: earlier base's return is a subtype of
// later base's return -> NOT conflicting, must stay accepted.
interface NarrowCallBase {
  (x: string): "a";
}
interface WideCallBase {
  (x: string): string;
}
interface CompatibleCallSub extends NarrowCallBase, WideCallBase {}

// Distinct parameter types across extends -> NOT conflicting, must stay accepted.
interface StrCallBase {
  (x: string): number;
}
interface NumCallBase {
  (x: number): string;
}
interface DisjointCallSub extends StrCallBase, NumCallBase {}

// Partial overlap (BaseA handles literal "a", BaseB handles general string):
// BaseB is STILL reachable for "b", so it is NOT shadowed — must stay accepted.
interface LitCallBase {
  (x: "a"): number;
}
interface GenCallBase {
  (x: string): string;
}
interface PartialOverlapSub extends LitCallBase, GenCallBase {}
declare const partialSub: PartialOverlapSub;
export function usePartialOverlap(): void {
  const n: number = partialSub("a");
  const s: string = partialSub("b");
}

// ---------------------------------------------------------------------------
// 2. Intra-declaration shadowed (unreachable) overloads
// ---------------------------------------------------------------------------

// Top-level function: wider overload listed before narrower.
function shadowedFn(x: string | number): string | number;
// @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
function shadowedFn(x: string): string;
function shadowedFn(x: string | number): string | number {
  return x;
}

// Proper order (narrower before wider): must NOT warn.
function orderedFn(x: string): string;
function orderedFn(x: string | number): string | number;
function orderedFn(x: string | number): string | number {
  return x;
}

// Class method: wider overload before narrower.
class ShadowedClass {
  m(x: string | number): string | number;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  m(x: string): string;
  m(x: string | number): string | number {
    return x;
  }

  constructor(x: string | number);
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  constructor(x: string);
  constructor(_x: string | number) {}
}

// Interface call/construct/method shadowed within one declaration.
interface ShadowedIface {
  (x: string | number): void;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  (x: string): void;
  new (x: string | number): object;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  new (x: string): object;
  m(x: string | number): void;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  m(x: string): void;
}

// Object type literal shadowed call/construct/method.
type ShadowedObj = {
  (x: string | number): void;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  (x: string): void;
  new (x: string | number): object;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  new (x: string): object;
  m(x: string | number): void;
  // @skjs-expect-warning This overload signature is shadowed by an earlier overload and can never be selected
  m(x: string): void;
};
export function useShadowedObj(o: ShadowedObj): void {
  o("a");
  const _x: object = new o("a");
  o.m("a");
}
