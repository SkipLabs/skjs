// A `break` or `continue` leaving a `try` with a `finally` runs the
// finalizer first, which the lowering does not state for jumps: refused. A
// `return` through a `finally` is lowered (`try-catch`).
function loop(log: () => void): number {
  let n: number = 0;
  while (n < 3) {
    try {
      break;
    } finally {
      log();
    }
  }
  return n;
}
