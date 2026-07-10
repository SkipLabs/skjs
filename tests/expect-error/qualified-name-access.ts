// A qualified name whose head is a class (or other non-namespace) is not a
// supported type. The error should be reported at the reference, like the
// "Cannot find type" error tsc-parity diagnostic beside it.
// @skjs-expect-error Cannot find type 'QualifiedBase.Missing'
function qualifiedClassMember(p: QualifiedBase.Missing): void {
  void p;
}

// @skjs-expect-error Qualified name access ('Missing') is not yet supported by SKJS
class QualifiedBase {
  x: number = 0;
}
