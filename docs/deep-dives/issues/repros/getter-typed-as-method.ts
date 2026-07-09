// repro for: getter-typed-as-method (docs/deep-dives/issues)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance)
// SKJS types a getter `get p(): T` as a method `p(): T` (the parser's
// isGetSet marker is never read by the checker). So calling the getter,
// c.p(), type-checks (a () => number returns number), but at runtime c.p
// already invoked the getter and yields the number, so c.p() calls a
// number -> TypeError. tsc rejects (TS6234, not callable).
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/getter-typed-as-method.ts BIN=target/host/dev/skjs

class C {
  get p(): number { return 5; }
}
function t(c: C): void {
  const n: number = c.p();   // accepted: c.p typed as () => number
  console.log(n.toFixed());  // runtime: c.p is not a function
}
t(new C());
