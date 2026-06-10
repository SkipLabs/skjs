// Test that a method call checks the receiver against the declared this
// parameter type.
//
// Today SKJS errors on the declaration itself ("TODO: support this
// parameter"), so the downstream call sites are not yet checked. The // TODO:
// comments mark errors that SKJS should report once this-parameter support
// lands.

class Obj {
  value: number = 1;
}
class Other {
  other: number = 2;
}

class MethodHolder {
  // @skjs-expect-error 'this' parameters are not yet supported by SKJS
  m(this: Obj, x: number): void {}
}

declare const holder: MethodHolder;

// TODO: SKJS should reject — MethodHolder is not assignable to this: Obj.
holder.m(1);

// Happy path: the receiver structurally satisfies this: Obj.
declare const objHolder: Obj & { m(this: Obj, x: number): void };
objHolder.m(1);

// Subclass receiver is allowed when the method expects a base-class this.
class Base {
  tag: string = "base";
}
class Derived extends Base {}

class BaseMethod {
  // @skjs-expect-error 'this' parameters are not yet supported by SKJS
  m(this: Base): void {}
}
declare const d: Derived & BaseMethod;
d.m();
