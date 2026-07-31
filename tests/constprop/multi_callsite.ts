// Context-insensitive call binding: a function analyzed under two callsites
// sees the *join* of the actuals at its entry, and the single summary that
// results flows back to both callsites.
//
// This is the core imprecision of `ContextInsensitive` (as opposed to `OneCFA`),
// and it is per-variable: only the formals that actually disagree are lost.
// (In the expectations a `top` binding shows up as an absent one, so `mixed`'s
// entry state is `{a=1.0}` with `b` widened away, and `scale`'s is `{}`.)

function scale(x: number): number {
  // Two callsites, two different actuals: `x` joins to `top`, so the summary is
  // `top` — even at the callsite whose argument alone would determine it.
  return x * 2;
}

function agree(x: number): number {
  // Two callsites with the *same* actual: the join is exact, so this stays 11.
  return x + 1;
}

function mixed(a: number, b: number): number {
  // Only `b` differs across the callsites; `a` is 1 in both, so it is retained
  // and only `b` (and hence the return) goes to `top`.
  return a + b;
}

function main(): number {
  const s1 = scale(1); // top, not 2
  const s2 = scale(3); // top, not 6
  const g1 = agree(10); // 11
  const g2 = agree(10); // 11
  const m1 = mixed(1, 2); // top
  const m2 = mixed(1, 5); // top
  return s1 + s2 + g1 + g2 + m1 + m2;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
