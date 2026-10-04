// Two values of `unknown` may both be of no kind the operator classifies.
function sameUnknown(left: unknown, right: unknown): boolean {
  return left === right;
}
