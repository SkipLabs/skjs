// prettier-ignore
// Regression test: Getters must be function definitions, not fields with initializers
class Foo {
  // @ts-expect-error Expected accessor definition
  get baz: string = "hello"; }