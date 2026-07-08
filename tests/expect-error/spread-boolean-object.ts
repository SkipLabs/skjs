// The `cond && {x: 1}` pattern has type `false | {x: number}`. When used as a
// spread, the primitive arm means the spread sometimes contributes nothing, so
// contributed fields become optional: the spread distributes as
// `(spread false) | (spread {x: 1})`, and the "did not fire" branch (the no-op
// primitive arm) leaves the accumulated object unchanged. TypeScript accepts
// this spread and makes contributed fields optional.

// Spread of `false | {y: number}` is accepted; `y` becomes optional.
function test(cond: boolean): { x: number; y?: number } {
  return { x: 0, ...(cond && { y: 1 }) };
}

// Soundness: the contributed field is optional, so assigning to a type that
// requires it must fail.
function testSoundness(cond: boolean): { x: number; y: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { x: 0, ...(cond && { y: 1 }) };
}

// `void` should never be observed, so a spread operand whose type includes
// it is rejected outright rather than treated as a sometimes-empty
// contribution the way `false | {...}` is.
declare function noop(): void;
function testVoid(cond: boolean): { x: number; y?: number } {
  // @skjs-expect-error Only an object type can be spread here
  return { x: 0, ...(cond ? noop() : { y: 1 }) };
}

// Spreading a string contributes its indexed characters as enumerable own
// properties (e.g. `{...'ab'}` is `{0: 'a', 1: 'b'}`), unlike other
// primitives, so it isn't a no-op the way `false | {...}` is — and tsc
// itself rejects spreading `string | {...}` outright.
function testString(cond: boolean): { x: number } {
  // @skjs-expect-error Only an object type can be spread here
  return { x: 0, ...(cond ? "ab" : { y: 1 }) };
}

// Soundness: when the spread type's object arm has no index at all, it might
// still carry an untyped excess property via width subtyping when it fires, so
// that field widens to Top (in ObjectSpreadState::merge) — hence rejected,
// since `Extra` declares neither `a` nor an index signature.
interface Extra {
  readonly z: string;
}
function testWidenObjectArm(cond: boolean, extra: Extra): { a: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 1, ...(cond && extra) };
}
