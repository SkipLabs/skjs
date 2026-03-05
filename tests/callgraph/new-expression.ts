// @skjs-callgraph
// fn:create: static:Foo.constructor

class Foo {
  value: number;
  constructor() {
    this.value = 0;
  }
}
function create(): Foo {
  return new Foo();
}
