/**
 * Exercise the source gate for mutable local declarations. The verifier must
 * report unsupported let syntax rather than treating y as an immutable const.
 */
function pick(x: string): string {
  let y = x;
  return y;
}
