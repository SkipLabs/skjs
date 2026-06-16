// Object-literal spread of a union-typed source. SKJS soundly approximates the
// spread by collapsing the branches into one open object, keeping every field
// but marking a branch-specific one optional (a value of another branch lacks
// it). TypeScript instead distributes spread over the union.
type AB = { a: number } | { b: string };

// The approximation yields `{ a?: number; b?: string }`, which is not
// assignable to the bare union (each member requires its field). TypeScript
// distributes and accepts this; matching it needs full spread distribution
// (tracked as a follow-up), so SKJS is sound but stricter here.
function spreadUnion(x: AB): AB {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}

// Into a Partial-style target the approximation is exact: both `a` and `b`
// survive as optional, so this is accepted (as in TypeScript).
function spreadIntoPartial(x: AB): { a?: number; b?: string } {
  return { ...x };
}
