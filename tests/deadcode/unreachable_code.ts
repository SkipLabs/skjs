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

// Top-level entrypoint reaching each function. Liveness treats calls as
// pass-through, so these non-returning callees leave top-level flow intact; the
// dead code lives inside each function's own body.
const r1 = afterReturn(1);
const r2 = afterThrow();
const r3 = afterInfiniteLoop();
