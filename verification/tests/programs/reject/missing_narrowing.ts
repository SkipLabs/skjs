// SKJS must reject: `x` can still be null on the returned path.
// This was the target of mutation M2 in the one-off emitter check described in
// verification/DESIGN.md: with STypes::isSub accepting a union member
// the target lacks, SKJS accepted it and the verifier caught it.
function pick(x: string | null): string {
  return x;
}
