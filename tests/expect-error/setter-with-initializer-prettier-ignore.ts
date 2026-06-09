// prettier-ignore
// Regression test: Setters must be function definitions, not fields with initializers
class Foo {
  // @skjs-expect-error Expected a getter or setter definition
  set bar: string = "hello"; }
