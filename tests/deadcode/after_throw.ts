// Intra-procedural dead code: statements after a `throw` are unreachable.
// `afterThrow` is reached from the top level, so its body is analyzed.

function afterThrow(): number {
  throw new Error("boom");
  const z = 1;
  return z;
}

const r = afterThrow();
