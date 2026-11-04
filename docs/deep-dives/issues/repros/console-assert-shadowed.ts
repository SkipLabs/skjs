// repro for: console-assert-narrowing, shadowed receiver (L-ASSERT)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// The spelling match does not consult the scope: a parameter named console
// with an arbitrary assert method triggers the same refinement, so any
// user-supplied method vouches for the condition. The stub's log delegates
// to the real console so the run shows s holding null at type string.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/console-assert-shadowed.ts BIN=target/host/dev/skjs

function g(
  console: { assert(b: boolean): void; log(v: string, w: string | null): void },
  x: string | null,
): void {
  console.assert(x !== null);
  const s: string = x;
  console.log("n =", s);
}
function run(): void {
  g(
    {
      assert: (_b: boolean): void => {},
      log: (v: string, w: string | null): void => {
        console.log(v, w);
      },
    },
    null,
  );
}
run();
