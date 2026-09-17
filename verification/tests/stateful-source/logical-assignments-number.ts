/**
 * `||=` on a number tests its truthiness, which the calculus does not model:
 * a logical assignment needs a Boolean target. SKJS, checking truthiness
 * only on Booleans, rejects this program; TypeScript accepts it, and the
 * verifier refuses its claims.
 */
function orNumber(box: { value: number }): number {
  return (box.value ||= 1);
}
