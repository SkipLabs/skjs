// A member TypeScript computes no value for is refused: its reverse mapping
// is keyed by its value at run time, which the object's lowering cannot name.
enum G {
  A = "abc".length,
  B = 4,
}
function four(): 4 {
  return G.B;
}
