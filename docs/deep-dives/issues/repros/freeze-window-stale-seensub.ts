// repro for: freeze-window-stale-memo-caches (docs/deep-dives/issues/freeze-window-stale-memo-caches.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/freeze-window-stale-seensub.ts BIN=target/host/dev/skjs

function g<B extends () => number[]>(b: B): number[] {
  return b();
}
function witness(): number {
  const a = [];
  a.push(1);
  const f = () => a;
  const r0 = g(f); // constraint validated with the element candidate = number (frozen, unsealed); memoized
  console.log(r0);
  a.push("s"); // the still-open candidate widens to number | string
  const r = g(f); // stale seenSub memo hit -> accepted; r : number[]
  const n: number | undefined = r[1];
  if (n !== undefined) {
    const m: number = n;
    return m; // m : number holds "s" at runtime
  }
  return 0;
}
console.log(witness());
