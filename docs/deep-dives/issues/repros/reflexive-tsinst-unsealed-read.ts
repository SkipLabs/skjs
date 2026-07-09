// repro for: reflexive-tsinst-fastpath-unsealed-read (docs/deep-dives/issues/reflexive-tsinst-fastpath-unsealed-read.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/reflexive-tsinst-unsealed-read.ts BIN=target/host/dev/skjs
// The isSub reflexive-TSInst fast path accepts Box<T1> <: Box<number> by
// peekRaw-reading T1's open candidate (number) WITHOUT sealing it; the
// later b.set("s") contravariantly widens T1, and r.get() — reading
// through the alias blessed by the fast path — returns "s" typed number.
// node: prints n = "s", typeof n = string. tsc rejects b.set("s") (TS2345).

class Box<T> {
  v: T;
  constructor(x: T) {
    this.v = x;
  }
  get(): T {
    return this.v;
  }
  set(x: T): void {
    this.v = x;
  }
}
function mk<T>(x: T): Box<T> {
  return new Box(x);
}
function main(): void {
  const one: number = 1;
  const b = mk(one);
  const r: Box<number> = b;
  b.set("s");
  const n: number = r.get();
  console.log("n =", JSON.stringify(n), "typeof n =", typeof n);
}
main();
