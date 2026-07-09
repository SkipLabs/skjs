// repro for: string-literal-escapes-undecoded, falsiness variant (L-LIT(iii))
// pin: 9108f339
// expect: accepted  (skjs check exits 0 — the unsound acceptance)
// A LineContinuation lexeme denotes "" (falsy) but isFalsy reads its
// non-empty lexeme as truthy, so the else of if(x) narrows to 0 and
// accepts z:0 while the branch runs at x = "". The canonical "" | 0
// control is correctly rejected (two falsy members).
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/string-continuation-falsiness.ts BIN=target/host/dev/skjs

function witness(x: "\
" | 0): void {
  if (x) {
  } else {
    const z: 0 = x; // accepted, but else runs at x = ""
    console.log(z);
  }
}
