// Test that detaching a method with a this parameter and calling it without
// binding is rejected (per TS: the call uses `this: void`).

// An interface, so `H & Ctx` is inhabited: two unrelated classes would share
// no instance (classes are nominal, see class-nominal.ts).
interface Ctx {
  value: number;
}

class H {
  method(this: Ctx, x: number): void {}
}

declare const h: H & Ctx;

function callOnReceiver(): void {
  // OK: the method is called with a compatible receiver.
  h.method(1);
}

function callDetached(): void {
  const g = h.method;
  // Detached call uses this: void, not this: Ctx.
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  g(1);
}
