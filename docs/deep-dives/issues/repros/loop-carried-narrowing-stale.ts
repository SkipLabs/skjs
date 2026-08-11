// repro for: loop-carried-narrowing-stale (L-LOOP-CARRIED)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// Scope::set checks an annotated binding's write only against the declared
// type (the annotation arm preempts the through-loop arm), so a narrowing
// established before the loop survives the back edge: iteration 2 reads
// x at the stale `string` while the store holds null.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/loop-carried-narrowing-stale.ts BIN=target/host/dev/skjs

declare function cond(): boolean;
function f(): void {
  let x: string | null = "hi";
  if (x !== null) {
    while (cond()) {
      const s: string = x;
      x = null;
      console.log(s);
    }
  }
}
console.log(f);
