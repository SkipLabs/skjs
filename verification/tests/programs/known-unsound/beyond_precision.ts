// SKJS accepts this program (issue #781). Both spellings denote the double
// 2^53, so `x === y` is TRUE at runtime and the branch returns a number
// through a `string` return type. SKJS reaches the branch with `x` narrowed
// to `never`, because it intersects the two literal spellings as text.
//
// The verifier identifies a numeric literal by the bit pattern of
// its double, so on that edge it derives `9007199254740992` for both `x` and
// `y`, and the edge into the branch cannot justify the claimed `never`.
//
// expect-reject: is not justified by every edge into it
function h(x: 9007199254740993, y: 9007199254740992): string {
  if (x === y) {
    return x;
  }
  return "b";
}
