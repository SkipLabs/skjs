// repro for: enum-concat-imprecise-fold (L-LIT-FOLD)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// The enum folder's string-concat arms build EFStr(a + b) from the raw
// operand lexeme with no precision gate, so a beyond-precision numeric
// operand creates a member literal whose spelling is not the runtime string:
// E.A is typed '"x1e-400"' but evaluates to "x0" (1e-400 underflows to 0
// before ToString). tsc types E.A as E and rejects the assignment.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/enum-concat-imprecise-fold.ts BIN=target/host/dev/skjs

enum E {
  A = "x" + 1e-400,
}
const t: "x1e-400" = E.A;
console.log(t);
