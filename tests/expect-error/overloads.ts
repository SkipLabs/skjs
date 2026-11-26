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

///////////////////////////////////////////////////////////////////////////////
// Phase 2: method, constructor, and call/construct-signature overloads
///////////////////////////////////////////////////////////////////////////////

// Class method overloads resolve first-match-wins; the implementation
// signature is excluded from the callable set. (The overloads share a return
// type so the implementation passes the strict TS2394 compatibility check.)
class MethodOvl {
  m(x: string): string;
  m(x: number): string;
  m(x: string | number): string {
    return typeof x === "string" ? x : "n";
  }
}

function testMethodOverloads(): void {
  const c = new MethodOvl();
  const a: string = c.m("hi");
  const b: string = c.m(42);
  // @skjs-expect-error No overload matches this call
  // @skjs-expect-error This expression was expected to be of type 'void' or ignorable
  c.m(true);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const wrong: number = c.m("hi");
}

// Constructor overloads form the `new` signature set.
class CtorOvl {
  constructor(x: string);
  constructor(x: number);
  constructor(x: string | number) {}
}

function testCtorOverloads(): void {
  const a = new CtorOvl("hi");
  const b = new CtorOvl(42);
  // @skjs-expect-error No overload matches this call
  // @skjs-expect-error This expression was expected to be of type 'void' or ignorable
  new CtorOvl(true);
}

// Static method overloads.
class StaticOvl {
  static s(x: string): string;
  static s(x: number): string;
  static s(x: string | number): string {
    return typeof x === "string" ? x : "n";
  }
}

function testStaticOverloads(): void {
  const a: string = StaticOvl.s("hi");
  const b: string = StaticOvl.s(42);
}

// Interface declaration merging accumulates overloads.
interface MergedI {
  f(x: string): number;
}
interface MergedI {
  f(x: number): string;
}

function testMergedInterface(i: MergedI): void {
  const a: number = i.f("hi");
  const b: string = i.f(42);
  // @skjs-expect-error No overload matches this call
  // @skjs-expect-error This expression was expected to be of type 'void' or ignorable
  i.f(true);
}

// Multiple call signatures in an object type literal form a call overload set.
function testCallSignatures(f: {
  (x: string): number;
  (x: number): string;
}): void {
  const a: number = f("hi");
  const b: string = f(42);
  // @skjs-expect-error No overload matches this call
  // @skjs-expect-error This expression was expected to be of type 'void' or ignorable
  f(true);
}

// Group rules for methods: duplicate implementation -> TS2393.
class DupImpl {
  m(x: string): void {}
  // @skjs-expect-error Duplicate function implementation
  m(x: number): void {}
}

// Implementation not last -> TS2391.
class NotLast {
  m(x: string): void {}
  // @skjs-expect-error Function implementation is missing or not immediately following the declaration
  m(x: number): void;
}

// Lone body-less method in a real class -> TS2391.
class LoneSig {
  // @skjs-expect-error Method implementation is missing
  m(x: string): void;
}

// Incompatible overload -> TS2394.
class Incompatible {
  // @skjs-expect-error Overload signature is not compatible with its implementation signature
  m(x: string): number;
  m(x: string): string {
    return "s";
  }
}

// Duplicate constructor implementations -> TS2392.
class DupCtor {
  constructor(x: string) {}
  // @skjs-expect-error Multiple constructor implementations are not allowed.
  constructor(x: number) {}
}

// Lone body-less constructor in a real class -> TS2391.
class LoneCtor {
  // @skjs-expect-error Constructor implementation is missing
  constructor(x: string);
}

// Interfaces need no implementation: body-less method groups are fine.
interface AmbientLike {
  m(x: string): number;
  m(x: number): string;
}

function testInterfaceGroup(i: AmbientLike): void {
  const a: number = i.m("hi");
  const b: string = i.m(42);
}
