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

// Rebinding an implicit-this method via .call/.apply/.bind. For now the
// implicit `this` is checked as the class instance, so rebinding to an
// unrelated receiver is rejected.
class Impl {
  v: number = 1;
  mm(a: number): number {
    return a;
  }
}
function implicitRebindOk(o: Impl): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  let _c: number = o.mm.call("anything", 1);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  let _a: number = o.mm.apply(42, [1]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bound: (a: number) => number = o.mm.bind(undefined);
  let _b: number = bound(1);
}

// .apply's argument array is omittable when the function takes no parameters.
function noArgs(this: Ctx): number {
  return 0;
}
function applyZeroArgOk(): number {
  return noArgs.apply(ctx);
}
