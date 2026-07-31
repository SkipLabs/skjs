// Whole-function reachability: `used` is called from top-level code, so it stays
// live. `orphan` is never called from any entrypoint, so the entire function is
// dead — every one of its blocks is reported, not just an intra-procedural tail.
// `usedByOrphanOnly` is called only from the dead `orphan`, so it too is
// unreachable from the program's real entrypoints.

function used(x: number): number {
  return x + 1;
}

function orphan(y: number): number {
  return usedByOrphanOnly(y);
}

function usedByOrphanOnly(z: number): number {
  return z * 2;
}

const r = used(5);
