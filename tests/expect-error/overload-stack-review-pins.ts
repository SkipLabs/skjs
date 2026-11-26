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

// 4. Optional `new?(): object` in an interface or object type literal is an
// optional method named `new`, NOT a construct signature (tsc TS2351 on `new x()`).
interface OptNewIface {
  new?(): object;
}
declare const oni: OptNewIface;
export function testOptNewIface(): void {
  // @skjs-expect-error This expression is not constructable
  const _o: object = new oni();
  const _m = oni.new;
}
type OptNewObj = {
  new?(): object;
};
declare const ono: OptNewObj;
export function testOptNewObj(): void {
  // @skjs-expect-error This expression is not constructable
  const _o: object = new ono();
  const _m = ono.new;
}

// 5. Constructor implementation not last in an overload group must error (TS2390).
class CtorImplNotLast {
  constructor(x: string) {}
  // @skjs-expect-error Constructor implementation is missing
  constructor(x: string);
}
