/**
 * Exercise the source gate for a mutable local with no initializer. An
 * initialized `let` is in the fragment, with a storage contract either written
 * or supplied by the producer and checked. This one has neither a value nor a
 * point at which it acquires one: after the declaration executes its value is
 * `undefined`, and admitting it needs definite assignment to show that a
 * suitable write precedes every read, through branches and captures.
 */
function pick(flag: boolean): boolean {
  let y: boolean;
  y = flag;
  return y;
}
