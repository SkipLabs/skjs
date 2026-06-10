// FIXME: missing callgraph edge for getter access (getter treated as method)
// skjs-callgraph
// fn:test: ctor:MyClass, method:MyClass.get:value
class MyClass {
  get value(): number {
    return 42;
  }
}
function test(): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new MyClass().value;
}
