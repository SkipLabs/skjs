// FIXME: accessor support must include the setter callgraph edge.
// skjs-callgraph
// fn:test: ctor:MyClass, method:MyClass.set:value
class MyClass {
  _value: number = 0;
  // @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
  set value(v: number): void {
    this._value = v;
  }
  get value(): number {
    return this._value;
  }
}
function test(): void {
  const obj = new MyClass();
  obj.value = 10;
}
