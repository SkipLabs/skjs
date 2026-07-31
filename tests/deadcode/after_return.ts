// Intra-procedural dead code: statements after a `return` are unreachable.
// `afterReturn` is reached from the top level, so its body is analyzed.

function afterReturn(x: number): number {
  return x;
  const y = x + 1;
  return y;
}

const r = afterReturn(1);
