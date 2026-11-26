// Pinning tests for overload-stack review findings before their fix commits.

// 1. Overloaded source -> rest-param target: a non-rest overload must NOT
// satisfy a target whose rest parameter accepts arbitrary argument counts
// (dispatching at runtime to a longer overload can return a different type).
declare function ovArity(x: string): string;
declare function ovArity(x: string, y: number): number;
export function testOverloadToRestTarget(): string {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const f: (x: string, ...rest: number[]) => string = ovArity;
  return f("a", 42);
}
// Single-signature source -> rest-param target stays accepted (no overload
// dispatch to mismatch).
export function testSingleToRestTarget(): string {
  const one = (x: string): string => x;
  const f: (x: string, ...rest: number[]) => string = one;
  return f("a", 42);
}

// 2. Interface `extends A, B`: bases must appear left-to-right (A before B),
// matching tsc (currently B overwrites/prepends ahead of A).
interface BaseA {
  (x: string): number;
}
interface BaseB {
  (x: string): string;
}
interface SubAB extends BaseA, BaseB {}
declare const subAB: SubAB;
export function testExtendsBaseOrder(): void {
  const a: number = subAB("hi");
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const b: string = subAB("hi");
}

// 3. Interface method named after a modifier keyword (e.g. `public(x: string): number`)
// must parse as a method named `public`, NOT as a call signature with modifier `public`.
interface ModMethodName {
  public(x: string): number;
}
declare const mmn: ModMethodName;
export function testModMethodName(): void {
  // Currently parses `public` as a modifier and `(...)` as a call signature.
  const wrongCall: number = mmn("hi");
  // @skjs-expect-error Property 'public' does not exist on this type
  const okMethod: number = mmn.public("hi");
}

// 4. Optional `new?(): object` in an interface or object type literal is an
// optional method named `new`, NOT a construct signature (tsc TS2351 on `new x()`).
interface OptNewIface {
  new?(): object;
}
declare const oni: OptNewIface;
export function testOptNewIface(): void {
  // Currently treated as a construct signature instead of an optional method.
  const _o: object = new oni();
  // @skjs-expect-error Property 'new' does not exist on this type
  const _m = oni.new;
}
type OptNewObj = {
  new?(): object;
};
declare const ono: OptNewObj;
export function testOptNewObj(): void {
  // Currently treated as a construct signature instead of an optional method.
  const _o: object = new ono();
  // @skjs-expect-error Property 'new' does not exist on this type
  const _m = ono.new;
}

// 5. Constructor implementation not last in an overload group must error (TS2391).
class CtorImplNotLast {
  constructor(x: string) {}
  // Currently silent because constructor() received allowMissing=true whenever
  // any constructor body existed, and checkMethodOverloadGroups didn't check
  // that the implementation comes last.
  constructor(x: string);
}
