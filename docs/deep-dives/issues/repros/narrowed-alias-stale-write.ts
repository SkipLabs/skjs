// repro for: narrowed-alias-stale-write (docs/deep-dives/issues/narrowed-alias-stale-write.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/narrowed-alias-stale-write.ts BIN=target/host/dev/skjs

function w(x: { f: number | null }): number {
  if (x.f !== null) {
    const y: { f: number } = x; // admitted: get narrowed to number, set gate contravariant
    x.f = null; // legal for x's declared set-type
    return y.f; // y's view is stale
  }
  return 0;
}

console.log(w({ f: 1 })); // Node prints: null
