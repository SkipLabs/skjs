// A NON-identity declaration named Closed: only the identity alias
// `type Closed<T> = T` (the recommended tsc-compat declaration, shipped in
// the SKJS stubs) is the closed-object operator; any other declaration named
// Closed keeps its ordinary meaning.
type Closed<T> = T | null;

function testNonIdentityClosedKeepsItsMeaning(): void {
  // TODO(Closed): today the 1-ary name is intercepted unconditionally, so
  // this rejects null; once recognition is by the identity-alias shape, the
  // user's `T | null` meaning applies and null is accepted.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: Closed<{ readonly a: number }> = null;
}
