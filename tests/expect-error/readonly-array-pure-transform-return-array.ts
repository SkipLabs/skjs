// `map` on `ReadonlyArray<T>` creates a fresh mutable array at runtime (same
// as on `Array<T>`), so its return type could be `Array<T2>` rather than
// `ReadonlyArray<T2>`. The stub is not yet updated to reflect this, so this
// is rejected; tsc accepts it since `Array<T>` and `ReadonlyArray<T>` are
// structurally compatible in this direction.
//
// `filter` and `slice` return `Array<T>` rather than `Array<T2>` — they
// reuse the receiver's own element type T, not a fresh generic — so widening
// them the same way would break `ReadonlyArray<T>`'s covariance in T: since
// `Array<T>` has invariant members (e.g. `push`), `ReadonlyArray<Sub>` would
// stop being assignable to `ReadonlyArray<Super>`. `map`'s T2 is a fresh
// per-call generic unrelated to T, so widening it is sound.

function testMapReturnsArray(xs: readonly number[]): number[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return xs.map((x: number) => x * 2);
}
