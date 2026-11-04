// repro for: beyond-precision-numeric-literals (docs/deep-dives/issues/beyond-precision-numeric-literals.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/beyond-precision-spurious-never.ts BIN=target/host/dev/skjs
// 9007199254740993 and 9007199254740992 are both the double 2^53, so
// x === y is true at runtime — but the two spellings are stored as
// distinct literal types, their intersection is a spurious never, and
// the live branch types x as never. node: prints s = 9007199254740992,
// typeof s = number. tsc rejects (the literals merge to one type).

function t(x: 9007199254740993 | "q", y: 9007199254740992 | "r"): void {
  if (x === y) {
    const z: never = x;
    const s: string = z;
    console.log("branch ran; s =", JSON.stringify(s), "typeof s =", typeof s);
  } else {
    console.log("branch not taken");
  }
}
t(9007199254740993, 9007199254740992);
