// repro for: evolving-capture-unchecked (L-CAPT-EVOLVE)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// A bare `let x = null` binding evolves, so its captured write is exempt
// from the L-CAPT check; after the closure runs, the binding still reads
// at null while holding "s". tsc accepts the same program (parity).
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/evolving-capture-unchecked.ts BIN=target/host/dev/skjs

function f(): void {
  let x = null;
  const w = (): void => {
    x = "s";
  };
  w();
  const n: null = x;
  console.log("n =", n);
}
f();
