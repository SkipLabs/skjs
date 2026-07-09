// repro for: stypes-inter-per-tag-zeroing (docs/deep-dives/issues/stypes-inter-per-tag-zeroing.md)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/stypes-inter-zeroing.ts BIN=target/host/dev/skjs

function t(x: "a" | 0, y: "a" | 1): void {
  if (x === y) {
    const z: never = x;
    const n: number = z;
    console.log(n);
  }
}
t("a", "a");
