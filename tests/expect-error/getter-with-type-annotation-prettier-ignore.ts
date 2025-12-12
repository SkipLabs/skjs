// prettier-ignore
// Regression test: Getters must be function definitions, not normal fields with type annotations
class Foo {
  // @ts-expect-error Expected accessor definition
  get foo: string; }