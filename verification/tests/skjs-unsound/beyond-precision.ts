/**
 * Future unsoundness target (issue #781): both numeric literals round to the
 * same JavaScript number. Equality can therefore return a number through the
 * string annotation, despite SKJS treating the branch input as never. The
 * current verifier rejects unsupported numeric types; that gate alone is not
 * an unsoundness proof.
 */
function h(x: 9007199254740993, y: 9007199254740992): string {
  if (x === y) {
    return x;
  }
  return "b";
}
