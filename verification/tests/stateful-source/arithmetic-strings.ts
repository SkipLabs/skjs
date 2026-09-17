/**
 * `+` on two strings is concatenation, which the calculus does not model: the
 * arithmetic rule needs two operands the number test answers for. SKJS
 * accepts this program; the verifier refuses its claims.
 */
function concat(s: string, t: string): string {
  return s + t;
}
