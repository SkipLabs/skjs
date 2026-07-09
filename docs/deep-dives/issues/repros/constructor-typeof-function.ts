// repro for: class-constructor-call-none-typeof (docs/deep-dives/issues/class-constructor-call-none-typeof.md)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/constructor-typeof-function.ts BIN=target/host/dev/skjs

class C {
  a: number = 1;
}
function g(): string {
  const F = C;
  if (typeof F === "function") {
    const s: string = F;
    return s;
  }
  return "not a function";
}
console.log(g());
