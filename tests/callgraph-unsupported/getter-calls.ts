// FIXME: accessor support must include the getter callgraph edge.
// skjs-callgraph
// fn:test: ctor:MyClass, method:MyClass.get:value
class MyClass {
  // @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
  get value(): number {
    return 42;
  }
}
function test(): number {
  return new MyClass().value;
}
