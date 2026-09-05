// SKJS must reject: inside `!(x !== null)` the value of x is null, not string.
// This was the target of mutation M1 in the one-off emitter check described in
// verification/DESIGN.md: with the `!` arm of evalCond no longer
// flipping its target, SKJS accepted it and the verifier caught it.
function neg(x: string | null): string {
  if (!(x !== null)) {
    return x;
  }
  return "n";
}
