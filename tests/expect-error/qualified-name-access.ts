// A qualified name whose head is a class (or other non-namespace) is not a
// supported type. The error is reported at the reference, alongside the
// "Cannot find type" diagnostic.
// @skjs-expect-error Cannot find type 'QualifiedBase.Missing'
// @skjs-expect-error Qualified name access ('Missing') is not yet supported by SKJS
function qualifiedClassMember(p: QualifiedBase.Missing): void {
  void p;
}

class QualifiedBase {
  x: number = 0;
}
