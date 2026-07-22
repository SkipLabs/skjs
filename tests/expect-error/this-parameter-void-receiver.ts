// A function that declares `this: void` / `this: undefined` ignores its
// receiver, so it is a free function: assignable to a no-`this` type, usable as
// a no-`this` callback, and its `.call`/`.apply`/`.bind` accept any receiver.
// This is sound only because the body may not observe `this`.

function voidThis(this: void): number {
  return 1;
}
function undefinedThis(this: undefined): number {
  return 1;
}

// Assignable to a no-`this` function type.
export function assignToNoThis(): number {
  const h: () => number = voidThis;
  return h();
}

// Usable as a no-`this` callback.
function callsCb(cb: () => number): number {
  return cb();
}
export function asCallback(): number {
  return callsCb(undefinedThis);
}

// `.call` accepts the natural `undefined` receiver.
function voidArg(this: void, a: number): number {
  return a;
}
export function viaCall(): number {
  return voidArg.call(undefined, 1);
}

// The body of a receiver-less function may NOT observe `this`: under a rebound
// receiver the declared `this: undefined` would be violated.
function usesThis(this: undefined): boolean {
  // @skjs-expect-error 'this' is not available in this context
  return this === undefined;
}

// A real `this: T` is not a free function.
function realThis(this: { x: number }): number {
  return this.x;
}
export function realStaysStrict(): number {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const h: () => number = realThis;
  return h();
}
