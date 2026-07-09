// repro for: stale-closure-reads-narrowing, field-level variant
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance)
// A closure body reads x.f under the creation-time narrowing (x.f non-null),
// but x.f is set to null before the closure runs. Accepted; at runtime
// x.f.m() is a TypeError on null. Field-level dual of the whole-local
// stale closure read; covered by no P1-P4 layer.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/field-read-in-closure.ts BIN=target/host/dev/skjs

function t(x: { f: { m(): void } | null }): void {
  if (x.f !== null) {
    const g = (): void => { x.f.m(); };
    x.f = null;
    g();
  }
}
