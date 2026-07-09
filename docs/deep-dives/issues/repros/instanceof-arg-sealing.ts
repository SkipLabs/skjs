// repro for: instanceof-type-argument-sealing (docs/deep-dives/issues/instanceof-type-argument-sealing.md)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/instanceof-arg-sealing.ts BIN=target/host/dev/skjs

class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}
function h(x: unknown): string {
  if (x instanceof Box) {
    const s: string = x.v;
    return s;
  }
  return "no";
}
console.log(h(new Box(42)));
