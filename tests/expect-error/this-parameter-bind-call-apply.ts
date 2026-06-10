// `.bind` / `.call` / `.apply` on functions that declare a `this` parameter.
// `.call(thisArg, ...args)` and `.apply(thisArg, args)` should check the
// receiver against the function's `this`; `.bind(thisArg)` should return the
// function with its `this` removed (OmitThisParameter). SKJS does not yet ship
// these signatures on function values: every access reports "Unbound field"
// until synthesis lands in the next commits.

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

// .call / .apply with a matching receiver should type-check.
function callApplyOk(): void {
  // @skjs-expect-error Unbound field: call
  withThis.call(ctx, 1);
  withThis.apply(ctx, [1]);
}

// .bind should strip the `this` parameter (OmitThisParameter).
function bindOk(): void {
  // @skjs-expect-error Unbound field: bind
  const bound: (x: number) => void = withThis.bind(ctx);
  bound(1);
}

// A wrong receiver should be rejected by .call.
function callWrongReceiver(): void {
  // @skjs-expect-error Unbound field: call
  withThis.call(notCtx, 1);
}

// ...and by .apply.
function applyWrongReceiver(): void {
  // @skjs-expect-error Unbound field: apply
  withThis.apply(notCtx, [1]);
}

// `this: void` accepts a direct call but should reject a non-void receiver via
// .call.
function noThisOk(): void {
  noThis(1);
}
function noThisCallWrong(): void {
  // @skjs-expect-error Unbound field: call
  noThis.call(ctx, 1);
}
