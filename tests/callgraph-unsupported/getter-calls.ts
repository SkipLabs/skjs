// FIXME: missing callgraph edge for getter access (getter treated as method)
class MyClass {
  get value(): number {
    return 42;
  }
}
function test(): number {
  // @skjs-expect-error Invalid return type
  return new MyClass().value;
}
