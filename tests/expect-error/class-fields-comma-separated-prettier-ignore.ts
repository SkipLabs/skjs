// prettier-ignore
// Regression test: Class fields cannot be comma-separated, must use semicolons
class Foo {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  a: string, b: number; }