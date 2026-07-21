// Every non-static method carries an implicit `this` (the enclosing class
// instance), including methods declared on classes that `extends` a parent and
// methods with no body (interfaces / ambient declarations). Detaching such a
// method and calling it without a receiver is rejected — SKJS is sound here
// where TS is not (tsc --strict accepts these).
//
// Staged: until the implicit `this` narrowing is lifted to extending/body-less
// methods, the detached-call rejections are documented with // TODO: markers.

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
  // TODO: reject — detached method on an extending class uses this: void.
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
  // TODO: reject — detached body-less interface method uses this: void.
  g(1);
}

// --- Subtyping is unaffected: a subclass is still assignable to its parent
// even though every method now carries an implicit this (two implicit class
// thises are mutually compatible in function-type subtyping). ---
function widensToBase(x: Derived): Base {
  return x;
}
