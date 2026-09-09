/**
 * A location under two invariant contracts at once. Both contracts denote the
 * same set of values, so the conjunction is inhabited and behaves as either
 * operand: the annotation lowers to a two-operand reference clause, and
 * covering shows it equivalent to the plain cell the producer claims.
 */
function sameContractTwice(seed: boolean): boolean {
  const cell: { value: boolean } & { value: boolean } = { value: seed };
  return cell.value;
}

/** The operands may be spelled differently and still coincide. */
function spelledTwoWays(seed: boolean): boolean {
  const cell: { value: boolean } & { value: true | false } = { value: seed };
  cell.value = false;
  return cell.value;
}
