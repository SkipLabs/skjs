// repro for: instanceof-array-mutable-top-view (docs/deep-dives/issues/instanceof-array-mutable-top-view.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/instanceof-array-mutable-top-view.ts BIN=target/host/dev/skjs

function corrupt(a: Array<number>): number {
  const x: unknown = a;

  if (x instanceof Array) {
    x[0] = "s"; // accepted: the installed view is mutable Array<top>
  }

  return a.reduce((acc: number, item: number): number => item, 0);
}

console.log(corrupt([1])); // Node prints: s
