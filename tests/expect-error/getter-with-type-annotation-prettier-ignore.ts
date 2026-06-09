// prettier-ignore
// Regression test: Getters must be function definitions, not normal fields with type annotations
class Foo {
  // @skjs-expect-error Expected a getter or setter definition
  get foo: string; }