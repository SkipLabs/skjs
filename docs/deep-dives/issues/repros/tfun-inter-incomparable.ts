// repro for: tfun-inter-incomparable-not-disjoint (docs/deep-dives/issues/tfun-inter-incomparable-not-disjoint.md)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/tfun-inter-incomparable.ts BIN=target/host/dev/skjs

function t(k: (s: string) => void, g: (n: number) => void): void {
  if (k === g) {
    const z: never = k;
    const n: number = z;
    console.log(n);
  }
}
function main(): void {
  const h = (x: unknown): void => {};
  t(h, h);
}
main();
