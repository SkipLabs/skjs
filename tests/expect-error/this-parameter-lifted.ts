// Every non-static method carries an implicit `this` (the enclosing class
// instance), including methods declared on classes that `extends` a parent and
// methods with no body (interfaces / ambient declarations). Detaching such a
// method and calling it without a receiver is rejected — SKJS is sound here
// where TS is not (tsc --strict accepts these).

// --- Method declared directly on an extending class ---
class Base {
  tag: string = "base";
}
class Derived extends Base {
  own(): void {
    let _ = this.tag;
  }
}

declare const d: Derived;

function ownCallOk(): void {
  d.own();
}

function ownDetached(): void {
  const g = d.own;
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  g();
}

// --- Body-less interface method ---
interface Handler {
  handle(x: number): void;
}

declare const h: Handler;

function ifaceCallOk(): void {
  h.handle(1);
}

function ifaceDetached(): void {
  const g = h.handle;
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  g(1);
}

// --- Subtyping is unaffected: a subclass is still assignable to its parent
// even though every method now carries an implicit this (two implicit class
// thises are mutually compatible in function-type subtyping). ---
function widensToBase(x: Derived): Base {
  return x;
}
