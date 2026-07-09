// A `let x: T | undefined` declared without an initializer may be read before
// assignment — TypeScript exempts it from the definite-assignment check
// (TS2454), treating it as implicitly `undefined`. skjs's used-before-assigned
// flow analysis flags it. Surfaced by the regenerated generated-examples
// (voting-system).
// FIXME(#765): skjs should exempt union-with-undefined lets; tsc accepts.
export function definiteAssignmentUnionUndefined(cond: boolean): number {
  let x: number | undefined;
  if (cond) x = 1;
  // @skjs-expect-error Variable 'x' is used before being assigned
  if (x === undefined) return 0;
  return x;
}
