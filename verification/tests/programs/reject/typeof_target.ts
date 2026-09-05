// SKJS must reject: on the fall-through path x is a number, not a string.
// This was the target of mutation M3 in the one-off emitter check described in
// verification/DESIGN.md: with evalTypeofEquality ignoring its target,
// SKJS accepted it and the verifier caught it.
function tag(x: string | number): string {
  if (typeof x === "string") {
    return "s";
  }
  return x;
}
