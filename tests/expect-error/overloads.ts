///////////////////////////////////////////////////////////////////////////////
// Function overloads: multiple same-named declarations form one overloaded
// function (tsc declaration merging). Call sites resolve first-match-wins in
// declaration order; assignability requires every target signature to be
// matched by some source overload; the implementation signature is not
// callable from outside and must be compatible with every overload
// (strictly, for soundness — tsc's loose "comparable" rule is a known hole,
// see docs/typescript-soundness-holes.md).
///////////////////////////////////////////////////////////////////////////////

// ---------------------------------------------------------------------------
// Ambient (`declare`) overloads: no implementation needed.
// ---------------------------------------------------------------------------

declare function g(x: string): number;
declare function g(x: number): string;

function testAmbientOverloadCalls(): void {
  const a: number = g("hi");
  const b: string = g(42);
  __SKJS_show(g);
}

// First matching overload wins, in declaration order.
declare function first(x: string): number;
declare function first(x: unknown): string;

function testFirstMatchWins(): void {
  const a: number = first("s");
  const b: string = first(1);
  __SKJS_show(first);
}

// Generic overload signatures resolve with inference per overload.
declare function id<T>(x: T): T;

function testGenericOverload(): void {
  const n: number = id(1);
  const s: string = id("a");
}

// An overloaded function is assignable to any single signature matched by
// one of its overloads (every target signature needs some source match).
function testOverloadAssignability(): void {
  const h: (x: string) => number = g;
  const k: (x: number) => string = g;
}

// ---------------------------------------------------------------------------
// Overloads with an implementation. The implementation must come last and
// be compatible with every overload signature.
// ---------------------------------------------------------------------------

function describe(x: string): string;
function describe(x: number): string;
function describe(x: string | number): string {
  return typeof x === "string" ? x : "num";
}

function testImplOverloadCalls(): void {
  const a: string = describe("hi");
  const b: string = describe(42);
  __SKJS_show(describe);
}

// ---------------------------------------------------------------------------
// Errors.
// ---------------------------------------------------------------------------

// No overload accepts a boolean argument.
function testNoOverloadMatches(): void {
  // @ts-expect-error No overload matches this call
  const r = g(true);
}

// The call resolves to the FIRST overload, so the result is number.
function testWrongReturnType(): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const c: boolean = g("hi");
}

// Not assignable: no overload accepts boolean and returns number.
function testBadAssignability(): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const bad: (x: boolean) => number = g;
}

// Duplicate function implementation (the two bodies).
function dup(x: string): number;
function dup(x: string): number {
  return 1;
}
// @ts-expect-error Duplicate function implementation
function dup(x: number): number {
  return 2;
}

// Missing implementation in a non-ambient group.
// @ts-expect-error Function implementation is missing or not immediately following the declaration
function noImpl(x: string): number;
function noImpl(x: number): string;

function testNoImplGroup(): void {
  const a: number = noImpl("hi");
}

// Implementation not compatible with the first overload: the body can
// return a string when called with a string, but the overload promises
// number. tsc accepts this via its unsound "comparable" rule (see
// docs/typescript-soundness-holes.md); SKJS rejects it.
// @skjs-expect-error Overload signature is not compatible with its implementation signature
function bad(x: string): number;
function bad(x: number): string;
function bad(x: string | number): number | string {
  return "oops";
}

// A function overload group still collides with a variable of the same name.
declare function collides(x: string): number;
declare function collides(x: number): string;
// @ts-expect-error Duplicate identifier 'collides'
const collides: number = 1;

// ---------------------------------------------------------------------------
// More group-shape and compatibility cases.
// ---------------------------------------------------------------------------

// A lone body-less non-ambient signature has no implementation (tsc TS2391).
// @skjs-expect-error Function implementation is missing or not immediately following the declaration
function lone(x: string): number;

// A group that mixes `declare` and plain members is NOT fully ambient: the
// plain member still needs an implementation (tsc TS2391).
// @skjs-expect-error Function implementation is missing or not immediately following the declaration
declare function mixed(x: string): number;
function mixed(x: number): number;

// The implementation-compatibility check is positional, not by parameter
// name: the implementation may use different parameter names than the
// overloads.
function named(x: string): string;
function named(value: string | number): string {
  return typeof value === "string" ? value : "n";
}

function testNamedImpl(): void {
  const a: string = named("hi");
}

// .call/.apply/.bind keep the whole overload set: each rebound call resolves
// first-match-wins over all overloads.
declare function g2(x: string): number;
declare function g2(x: number): string;

function testCallApplyBind(): void {
  const a: number = g2.call(undefined, "hi");
  const b: string = g2.call(undefined, 42);
  const c: number = g2.apply(undefined, ["hi"]);
  const d: string = g2.bind(undefined)(42);
}
