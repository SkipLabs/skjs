/**
 * The other operand is a call, which may write the tested cell between the
 * read and the branch: with `o` below, `callOperand` returns 0 from a function
 * declared to return 1. TypeScript narrows the read anyway; SKJS rejects the
 * program, and the verifier refuses TypeScript's claim because the read is
 * not saved across a call.
 */
function callOperand(x: { value: 0 | 1 }, zeroOf: () => 0): 1 {
  if (x.value !== zeroOf()) return x.value;
  return 1;
}
