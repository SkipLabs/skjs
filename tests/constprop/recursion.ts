// Recursion: the fixpoint must terminate. Both recursive calls are resolved
// interprocedurally, even `fact`'s, which is nested inside `n * ...` (nested
// calls are resolved through `evalExpr`). So each function's parameter `n`
// widens to `top` across the recursion, both branches stay live, and the base
// case is reachable. `fact` multiplies by a recursively-`top` result, so its
// summary is `top`; `loopConst` returns 7 on every path, so it converges to 7.

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
