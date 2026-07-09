// repro for: string-literal-escapes-undecoded (docs/deep-dives/issues/string-literal-escapes-undecoded.md)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/string-escapes-injectivity.ts BIN=target/host/dev/skjs

function t(x: "a" | 0): void {
  if (x === "\x61") {
    const z: 0 = x;
    console.log("true branch, z =", z, "typeof:", typeof z);
  } else {
    console.log("else branch, x =", x);
  }
}
t("a");
