// Document target behavior for .bind / .call / .apply on functions that
// declare a `this` parameter.
//
// Today SKJS does not ship `.bind`, `.call`, `.apply` signatures on function
// values (the fields report "Unbound field"), and declarations with a this
// parameter report "TODO: support this parameter". This file encodes the
// intended behavior; annotations will be filled in when support lands.

class Ctx {
  value: number = 1;
}
class NotCtx {
  other: number = 2;
}

// @skjs-expect-error TODO: support this parameter
function withThis(this: Ctx, x: number): void {}

// TODO: Once implemented, `withThis.call(ctx, 1)` should succeed and
// `withThis.call(wrong, 1)` should reject the receiver.
// TODO: `withThis.apply(ctx, [1])` should succeed; `withThis.apply(wrong, [1])`
// should reject.
// TODO: `withThis.bind(ctx)` should return a function whose this parameter is
// stripped (OmitThisParameter) so `bound(1)` type-checks.

// A function declaring `this: void` must not be callable with `.call` on a
// non-void receiver.
// @skjs-expect-error TODO: support this parameter
function noThis(this: void, x: number): void {}

// TODO: `noThis(1)` should succeed; `noThis.call(ctx, 1)` should reject.
