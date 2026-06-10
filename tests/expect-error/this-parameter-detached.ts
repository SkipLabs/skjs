// Test that detaching a method with a this parameter and calling it without
// binding is rejected (per TS: the call uses `this: void`).
//
// Today SKJS errors on the method declaration itself ("TODO: support this
// parameter"), so the detached-call case is only documented here with
// // TODO: markers until this-parameter support lands.

class Ctx {
  value: number = 1;
}

class H {
  // @skjs-expect-error 'this' parameters are not yet supported by SKJS
  method(this: Ctx, x: number): void {}
}

declare const h: H & Ctx;

function callOnReceiver(): void {
  // OK: the method is called with a compatible receiver.
  h.method(1);
}

function callDetached(): void {
  const g = h.method;
  // TODO: SKJS should reject — `g()` uses this: void, not this: Ctx.
  g(1);
}
