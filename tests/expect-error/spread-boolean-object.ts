// The `cond && {x: 1}` pattern has type `false | {x: number}`. When used as a
// spread, the primitive arm means the spread sometimes contributes nothing, so
// contributed fields should be optional. TypeScript accepts this spread and
// makes contributed fields optional.

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
