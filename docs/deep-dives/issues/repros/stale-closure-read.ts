// repro for: stale-closure-reads-narrowing (docs/deep-dives/issues/stale-closure-reads-narrowing.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/stale-closure-read.ts BIN=target/host/dev/skjs

function t(): void {
  let x: string | null = "a";
  if (x !== null) {
    const g = (): number => x.length;
    x = null;
    console.log(g());
  }
}
t();
