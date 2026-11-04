// repro for: cabsent-brand-laundering (F-CABSENT)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// isSubCallability accepts (CPresent, CUnknown) and (CUnknown, CAbsent), so a
// callable passes Function -> {} -> C in two accepted steps; C's CAbsent
// brand is then trusted by typeof "function" narrowing, which drops the
// taken branch to never.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/cabsent-brand-laundering.ts BIN=target/host/dev/skjs

class C {}
function h(g: () => void): void {
  const o: {} = g;
  const c: C = o;
  if (typeof c === "function") {
    const n: never = c;
    console.log("branch taken at never:", n);
  }
}
h((): void => {});
