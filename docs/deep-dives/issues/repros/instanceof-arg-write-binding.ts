// repro for: instanceof-type-argument-sealing, write side (docs/deep-dives/issues/instanceof-type-argument-sealing.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/instanceof-arg-write-binding.ts BIN=target/host/dev/skjs

class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function w(a: Box<number>): number {
  const x: unknown = a;

  if (x instanceof Box) {
    x.v = "s"; // accepted: the write binds the fresh unbound argument to string
  }

  return a.v;
}

console.log(w(new Box(1))); // Node prints: s
