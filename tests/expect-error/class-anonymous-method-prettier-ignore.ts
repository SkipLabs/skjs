// prettier-ignore
// Regression test: Classes cannot have anonymous methods (call signatures)
class Foo {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  (): string; }