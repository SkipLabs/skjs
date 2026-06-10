// prettier-ignore
// Regression test: Classes cannot have anonymous methods (call signatures)
class Foo {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  (): string; }