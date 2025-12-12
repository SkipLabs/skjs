// prettier-ignore
// Regression test: Setters must be function definitions, not fields with initializers
class Foo {
  // @ts-expect-error Expected accessor definition
  set bar: string = "hello"; }
