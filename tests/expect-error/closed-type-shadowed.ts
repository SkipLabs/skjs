// A file-local, NON-identity declaration named Closed. Include resolution is
// stubs-first (a stub-declared name shadows a file-local redefinition,
// engine-wide — the same happens for e.g. StringRecord), so the reference
// below resolves to the stubs' identity alias `type Closed<T> = T` and keeps
// the builtin closed-object meaning: the local `T | null` is inert and null
// is rejected. SKJS recognizes the operator by that identity-alias SHAPE, not
// by bare name: in a project whose stubs do not declare Closed, a local
// non-identity declaration like this one would keep its own meaning.
type Closed<T> = T | null;

function testNonIdentityClosedIsShadowedByStub(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: Closed<{ readonly a: number }> = null;
}
