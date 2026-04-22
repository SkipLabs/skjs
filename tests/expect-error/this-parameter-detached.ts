// Test that detaching a method with a this parameter and calling it without
// binding is rejected (per TS: the call uses `this: void`).

class Ctx {
  value: number = 1;
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
