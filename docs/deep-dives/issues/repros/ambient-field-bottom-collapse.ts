// repro for: ambient-unannotated-field-bottom (docs/deep-dives/issues)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance)
// An un-annotated field on an ambient class expands to a placeholder TSInst
// whose head-expansion collapses to bottom; bottom <: everything, so the read
// c.x is accepted into string AND never. tsc --strict rejects at TS7008.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/ambient-field-bottom-collapse.ts BIN=target/host/dev/skjs

declare class C { x }
declare const c: C;
function f(): void {
  const y: string = c.x;   // accepted: c.x reads as bottom
  const n: never = c.x;    // also accepted — proof the read type is bottom
  console.log(y, n);
}
