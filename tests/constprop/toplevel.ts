// Module top-level code is the real entrypoint, and now has its own CFG. The
// top-level constant `K` flows through the call `scale(K)`, so `scale` is
// analyzed with `n = 3` and returns 6; `result` is bound to 6 in the top-level
// environment. Without a top-level CFG, `scale` would never be seen with a
// concrete argument here.

const K = 3;

function scale(n: number): number {
  return n * 2;
}

const result = scale(K);
