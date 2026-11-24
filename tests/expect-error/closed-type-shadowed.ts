// A file-local, NON-identity declaration named Closed does not change the
// meaning of Closed<...>: the reference keeps the builtin closed-object
// semantics, so null (an inhabitant of the local `T | null` reading) is
// rejected. The collision with the builtin alias is itself reported
// (TS2300, issue #887).
// @skjs-expect-error Duplicate identifier 'Closed'
type Closed<T> = T | null;

function testNonIdentityClosedStaysBuiltin(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: Closed<{ readonly a: number }> = null;
}
