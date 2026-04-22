// Test that a method call checks the receiver against the declared this
// parameter type.

class Obj {
  value: number = 1;
}
class Other {
  other: number = 2;
}

class MethodHolder {
  m(this: Obj, x: number): void {}
}

declare const holder: MethodHolder;

// MethodHolder is not assignable to this: Obj.
// @skjs-expect-error The 'this' context is not assignable to method's 'this' type
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
  m(this: Base): void {}
}
declare const d: Derived & BaseMethod;
d.m();
