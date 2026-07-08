// The `cond && {x: 1}` pattern has type `false | {x: number}`. When used as a
// spread, the primitive arm means the spread sometimes contributes nothing, so
// contributed fields should be optional. TypeScript accepts this spread and
// makes contributed fields optional. skjs currently rejects any spread whose
// source is a union with a non-object arm.

// Spread of `false | {y: number}`: currently rejected; should be accepted with
// `y` optional.
function test(cond: boolean): { x: number; y?: number } {
  // @skjs-expect-error Only an object type can be spread here
  return { x: 0, ...(cond && { y: 1 }) };
}

// Soundness: the contributed field should be optional, so assigning to a type
// that requires it must fail. (Currently rejected for the wrong reason — the
// whole spread is refused.)
function testSoundness(cond: boolean): { x: number; y: number } {
  // @skjs-expect-error Only an object type can be spread here
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
// that field widens to Top — hence this should be rejected, since `Extra`
// declares neither `a` nor an index signature. (Currently rejected because the
// whole spread is refused.)
interface Extra {
  readonly z: string;
}
function testWidenObjectArm(cond: boolean, extra: Extra): { a: number } {
  // @skjs-expect-error Only an object type can be spread here
  return { a: 1, ...(cond && extra) };
}
