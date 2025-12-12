// prettier-ignore
// Regression test: Class fields cannot be comma-separated, must use semicolons
class Foo {
  // @ts-expect-error Expected token a variable name or a number or - or ' or "
  a: string, b: number; }