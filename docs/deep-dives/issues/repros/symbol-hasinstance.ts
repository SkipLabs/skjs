// repro for: symbol-hasinstance-narrowing (docs/deep-dives/issues/symbol-hasinstance-narrowing.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/symbol-hasinstance.ts BIN=target/host/dev/skjs

class C {
  a: number = 1;
  static [Symbol.hasInstance](x: unknown): boolean {
    return true;
  }
}
function f(x: unknown): number {
  if (x instanceof C) {
    return x.a;
  }
  return 0;
}
console.log(f("not a C"));
