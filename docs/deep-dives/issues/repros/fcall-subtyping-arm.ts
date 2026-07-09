// repro for: class-constructor-call-none-typeof, subtyping-arm facet (F-CALL)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance)
// isSubOptTFuns accepts (Some(sig), None) — a callable is a subtype of {}.
// Then typeof o === "function" drops the call=None branch, narrowing o to
// never, so const n: never = o is accepted while o holds a function.
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/fcall-subtyping-arm.ts BIN=target/host/dev/skjs

function h(g: () => void): void {
  const o: {} = g;
  if (typeof o === "function") { const n: never = o; console.log(n); }
}
