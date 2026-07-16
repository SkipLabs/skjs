// A `let x: T | undefined` declared without an initializer may be read before
// assignment — TypeScript exempts it from the definite-assignment check
// (TS2454), treating it as implicitly `undefined`: `bindType` now checks
// whether the declared type accepts `undefined` (via `undefined <: ty`) and
// marks the binding initialized from the start if so, matching what a real
// read before assignment actually observes at runtime. Surfaced by the
// regenerated generated-examples (voting-system).
export function definiteAssignmentUnionUndefined(cond: boolean): number {
  let x: number | undefined;
  if (cond) x = 1;
  if (x === undefined) return 0;
  return x;
}
