// Functions containing dead code: statements after a return, after a throw, and
// after an infinite loop are all unreachable.

function afterReturn(x: number): number {
  return x;
  const y = x + 1;
  return y;
}

function afterThrow(): number {
  throw new Error("boom");
  const z = 1;
  return z;
}

function afterInfiniteLoop(): number {
  while (true) {
    let x = 1;
  }
  return 0;
}
