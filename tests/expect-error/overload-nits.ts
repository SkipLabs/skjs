///////////////////////////////////////////////////////////////////////////////
// Pinning tests for overload nits before their fixes land.
// Each section pins the current behavior so the subsequent fix commit visibly
// flips the pin to the intended behavior.
///////////////////////////////////////////////////////////////////////////////

// ---------------------------------------------------------------------------
// 1. Construct signatures with explicit `this` parameter (TS2681)
// ---------------------------------------------------------------------------

// @ts-expect-error A constructor cannot have a 'this' parameter
type NewFnWithThis = new (this: { a: number }, x: string) => { a: number };
type NewObjWithThis = {
  // @ts-expect-error A constructor cannot have a 'this' parameter
  new (this: { a: number }, x: string): { a: number };
};
interface NewIfaceWithThis {
  // @ts-expect-error A constructor cannot have a 'this' parameter
  new (this: { a: number }, x: string): { a: number };
}

function useNewWithThis(
  c1: NewFnWithThis,
  c2: NewObjWithThis,
  c3: NewIfaceWithThis,
): void {
  // No cascading `this` mismatch at construction sites once `this` is dropped.
  const r1: { a: number } = new c1("hi");
  const r2: { a: number } = new c2("hi");
  const r3: { a: number } = new c3("hi");
}

// ---------------------------------------------------------------------------
// 2. Interleaved overload contiguity (TS2391 / TS2390)
// ---------------------------------------------------------------------------

// Interleaving another declaration between an overload signature and its
// implementation is rejected (TS2391 for functions/methods, TS2390 for ctors).
// @ts-expect-error Function implementation is missing or not immediately following the declaration
function interleavedFn(x: string): string;
const sepFn = 1;
function interleavedFn(x: string): string {
  return x;
}

function interleavedTwoSigs(x: string): string;
// @ts-expect-error Function implementation is missing or not immediately following the declaration
function interleavedTwoSigs(x: number): number;
const sepFn2 = 1;
function interleavedTwoSigs(x: string | number): string | number {
  return x;
}

// Ambient declarations separated by another declaration are legal in tsc.
declare function ambientSeparated(x: string): string;
const sepAmbient = 1;
declare function ambientSeparated(x: number): number;

class InterleavedMethod {
  // @ts-expect-error Function implementation is missing or not immediately following the declaration
  m(x: string): string;
  x: number = 1;
  m(x: string): string {
    return x;
  }
}

class InterleavedCtor {
  // @ts-expect-error Constructor implementation is missing
  constructor(x: string);
  x: number = 1;
  constructor(x: string) {}
}

// Interface methods separated by a field are legal in tsc.
interface InterfaceSeparated {
  m(x: string): string;
  x: number;
  m(x: number): number;
}

// ---------------------------------------------------------------------------
// 3. Calls and `new` through callable/constructable intersections (A & B)
// ---------------------------------------------------------------------------

type CallA = (x: string) => number;
type CallB = (x: number) => string;
type CallAB = CallA & CallB;

function useCallInter(f: CallAB): void {
  const n: number = f("hi");
  const s: string = f(42);
  // @ts-expect-error No overload matches this call
  const bad = f(true);
}

type NewA = new (x: string) => { a: string };
type NewB = new (x: number) => { b: number };
type NewAB = NewA & NewB;

function useNewInter(C: NewAB): void {
  const a: { a: string } = new C("hi");
  const b: { b: number } = new C(42);
  // @ts-expect-error No overload matches this call
  const bad = new C(true);
}

type ObjCallA = { (x: string): number; tag: "a" };
type ObjCallB = { (x: number): string; extra: boolean };
type ObjCallAB = ObjCallA & ObjCallB;

function useObjCallInter(o: ObjCallAB): void {
  const n: number = o("hi");
  const s: string = o(42);
  const t: "a" = o.tag;
  const e: boolean = o.extra;
}

// ---------------------------------------------------------------------------
// 4. Contextual typing of closure arguments per candidate overload
// ---------------------------------------------------------------------------

declare function onEvent(ev: "num", cb: (n: number) => number): number;
declare function onEvent(ev: "str", cb: (s: string) => number): number;

function testOnEventNum(): void {
  const r: number = onEvent("num", (x) => x + 1);
}

function testOnEventStr(): void {
  const r: number = onEvent(
    "str",
    // @skjs-expect-error Property 'length' does not exist on this type
    (x) => x.length,
  );
}

declare function withOptionalCb(x: string): number;
declare function withOptionalCb(x: string, cb: (s: string) => number): number;

function testOptionalCb(): void {
  // @skjs-expect-error A parameter must have an explicit type annotation
  const n: number = withOptionalCb("hi", (s) => s.length);
}

// ---------------------------------------------------------------------------
// 5. Merged-interface overload order (later declarations should come first)
// ---------------------------------------------------------------------------

interface MergeOrder {
  (x: string): number;
  (x: string | number): boolean;
  new (x: string): { from: "first" };
  m(x: string): number;
}
interface MergeOrder {
  (x: "a"): "second-1";
  (x: "a" | "b"): "second-2";
  new (x: string | number): { from: "second" };
  m(x: string | number): string;
}

function testMergeOrder(x: MergeOrder): void {
  // Currently first declaration wins; tsc resolves later declarations first.
  const r1: number = x("a");
  const r2: number = x("b");
  const r3: number = x("c");
  const r4: boolean = x(1);
  const c1: { from: "first" } = new x("hi");
  const m1: number = x.m("hi");
}
