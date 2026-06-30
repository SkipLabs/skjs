// The `cond && {x: 1}` pattern has type `false | {x: number}`. When used as a
// spread, the primitive arm means the spread sometimes contributes nothing, so
// contributed fields should be optional. TypeScript accepts this spread and
// makes contributed fields optional.
//
// Currently rejected; will be accepted after the spread check is updated.

function test(cond: boolean): { x: number; y?: number } {
  // @skjs-expect-error Only an object type can be spread here
  return { x: 0, ...(cond && { y: 1 }) };
}
