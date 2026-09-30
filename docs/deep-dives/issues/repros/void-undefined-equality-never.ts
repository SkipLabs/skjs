// repro for: void-undefined-equality-never (L-SEQ)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// A void-typed operand of === draws only a warning, so refinement runs; the
// RHS is a variable (not the `undefined` literal), so the generic equality
// rule intersects the void and undefined units as disjoint, narrowing x to
// never in a branch the runtime takes with x === undefined.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/void-undefined-equality-never.ts BIN=target/host/dev/skjs

function g(): void {}
function f(y: undefined): void {
  const x = g();
  if (x === y) {
    const n: never = x;
    console.log("branch taken at type never:", n);
  }
}
f(undefined);
