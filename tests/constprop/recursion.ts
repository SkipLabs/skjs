// Recursion: the fixpoint must terminate. `fact`'s recursive call is nested
// inside `n * ...`, which folds to `top` and is not resolved interprocedurally,
// so `fact` is only ever seen with `n = 5` (from `main`); its base case is thus
// pruned (5 <= 0 is false) and its summary is `top`. `loopConst`'s recursive
// call is a bare `return` operand, so it *is* resolved: `n` widens to `top`,
// both branches stay live, and every path returns 7, so it converges to 7.

function fact(n: number): number {
  if (n <= 0) {
    return 1;
  }
  return n * fact(n - 1);
}

function loopConst(n: number): number {
  if (n <= 0) {
    return 7;
  }
  return loopConst(n - 1);
}

function main(): number {
  const a = fact(5);
  const b = loopConst(3);
  return b;
}
