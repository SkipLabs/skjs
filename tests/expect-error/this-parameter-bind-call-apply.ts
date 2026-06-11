// `.bind` / `.call` / `.apply` on functions that declare a `this` parameter.
// `.call(thisArg, ...args)` and `.apply(thisArg, args)` check the receiver
// against the function's `this`; `.bind(thisArg)` returns the function with its
// `this` removed (OmitThisParameter). SKJS synthesizes these from the call
// signature for non-generic functions with required positional parameters.

class Ctx {
  value: number = 1;
}
class NotCtx {
  other: number = 2;
}

function withThis(this: Ctx, x: number): void {}
function noThis(this: void, x: number): void {}

declare const ctx: Ctx;
declare const notCtx: NotCtx;

// .call / .apply with a matching receiver type-check.
function callApplyOk(): void {
  withThis.call(ctx, 1);
  withThis.apply(ctx, [1]);
}

// .bind strips the `this` parameter (OmitThisParameter).
function bindOk(): void {
  const bound: (x: number) => void = withThis.bind(ctx);
  bound(1);
}

// A wrong receiver is rejected by .call.
function callWrongReceiver(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  withThis.call(notCtx, 1);
}

// ...and by .apply.
function applyWrongReceiver(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  withThis.apply(notCtx, [1]);
}

// `this: void` accepts a direct call but rejects a non-void receiver via .call.
function noThisOk(): void {
  noThis(1);
}
function noThisCallWrong(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  noThis.call(ctx, 1);
}

// .call / .bind carry the function's optional and rest parameters.
function optional(this: Ctx, a: number, b?: string): void {}
function variadic(this: Ctx, a: number, ...rest: boolean[]): void {}

function optionalRestOk(): void {
  optional.call(ctx, 1);
  optional.call(ctx, 1, "x");
  variadic.call(ctx, 1, true, false);
  const bound: (a: number, b?: string) => void = optional.bind(ctx);
  bound(1);
}

function optionalCallWrongArg(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  optional.call(ctx, 1, 2);
}

// An implicit class `this` requires the `.call`/`.apply`/`.bind` receiver to be
// the class instance: rebinding to an unrelated receiver is rejected (sound; TS
// resolves an implicit method's ThisParameterType to `unknown` and accepts any
// receiver, but the body reads the class's fields off the rebound `this`).
class Impl {
  v: number = 1;
  mm(a: number): number {
    return this.v + a;
  }
}
function implicitRebindCompatibleOk(o: Impl, o2: Impl): void {
  let _c: number = o.mm.call(o2, 1);
  let _a: number = o.mm.apply(o2, [1]);
  const bound: (a: number) => number = o.mm.bind(o2);
  let _b: number = bound(1);
}
function implicitRebindWrongReceiver(o: Impl): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  let _ = o.mm.call("anything", 1);
}

// .apply's argument array is omittable when the function takes no parameters.
function noArgs(this: Ctx): number {
  return 0;
}
function applyZeroArgOk(): number {
  return noArgs.apply(ctx);
}

// Partial application is not modeled: extra bound args to .bind are rejected
// (a never[] rest) rather than silently ignored, like TS's TS2554.
function bindExtraArgsRejected(o: Impl): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  let _ = o.mm.bind(o, 99);
}
