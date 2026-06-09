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
