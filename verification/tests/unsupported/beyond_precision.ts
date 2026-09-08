// SKJS accepts this program (issue #781). Both spellings denote the double
// 2^53, so `x === y` is TRUE at runtime and the branch returns a number
// through a `string` return type. SKJS reaches the branch with `x` narrowed
// to `never`, because it intersects the two literal spellings as text.
//
// Numeric types and equality are outside the current verifier. This fixture
// records a future soundness target; its current rejection is only a gate.
function h(x: 9007199254740993, y: 9007199254740992): string {
  if (x === y) {
    return x;
  }
  return "b";
}
