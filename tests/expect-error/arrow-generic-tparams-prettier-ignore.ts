// prettier-ignore
// Generic arrow with multiple type parameters — currently typechecker
// doesn't add tparams to scope so T is reported unknown.

function testArrowGenericMulti(): void {
  // @skjs-expect-error Type T not found
  const f = <T, U>(x: T, y: U): void => { void x; void y; };
  void f;
}
