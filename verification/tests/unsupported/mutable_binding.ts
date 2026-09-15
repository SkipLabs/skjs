/**
 * Exercise the source gate for an unannotated mutable local. A `let` is in the
 * fragment only with a stated storage contract: what the initializer happens
 * to produce is not what the binding may later hold, so the gate refuses to
 * infer one rather than treating y as an immutable const or inventing a type.
 */
function pick(x: string): string {
  let y = x;
  return y;
}
