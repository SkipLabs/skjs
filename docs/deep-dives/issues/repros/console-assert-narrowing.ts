// repro for: console-assert-narrowing (L-ASSERT)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// console.assert(e) is matched by spelling and applies the true refinement
// of e, but at runtime a failed assertion logs and continues, so the code
// after it runs with the condition false: s holds null at type string.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/console-assert-narrowing.ts BIN=target/host/dev/skjs

function f(x: string | null): void {
  console.assert(x !== null);
  const s: string = x;
  console.log(s.length);
}
f(null);
