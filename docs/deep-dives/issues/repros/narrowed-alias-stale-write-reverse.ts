// repro for: narrowed-alias-stale-write, reverse direction (docs/deep-dives/issues/narrowed-alias-stale-write.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/narrowed-alias-stale-write-reverse.ts BIN=target/host/dev/skjs

function w(x: { f: number | null }): number {
  if (x.f !== null) {
    const y: { f: number | null } = x; // same-type alias, trivially admitted
    y.f = null; // legal for y's set-type
    return x.f; // x's narrowed view is stale
  }
  return 0;
}

console.log(w({ f: 1 })); // Node prints: null
