// Closed<T> used WITHOUT the tsc-compat identity alias: the builtin must work
// with no declaration at all (tsc rejects this whole file with TS2304 "Cannot
// find name 'Closed'" — this is the SKJS-only surface).
//
// Tests-first BASELINE: on current main the name does not resolve, so each use
// is pinned to "Cannot find type"; the feature commit removes these errors.

function testUndeclaredClosedAnnotation(): void {
  // TODO(Closed): the builtin resolves this without any declaration.
  // @skjs-expect-error Cannot find type 'Closed'
  const x: Closed<{ readonly a: number }> = { a: 1 };
}

function testUndeclaredClosedSecondUse(): void {
  // TODO(Closed): the builtin resolves this without any declaration.
  // @skjs-expect-error Cannot find type 'Closed'
  const y: Closed<{ b: string }> = { b: "s" };
}
