// FIXME: missing callgraph edge for setter access (setter treated as method)
// skjs-callgraph
// fn:test: ctor:MyClass, method:MyClass.set:value
class MyClass {
  _value: number = 0;
  set value(v: number): void {
    this._value = v;
  }
  get value(): number {
    return this._value;
  }
}
function test(): void {
  const obj = new MyClass();
  // @skjs-expect-error Type is not assignable to the assignment target's type
  obj.value = 10;
}
