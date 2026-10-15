// An object type with a construct signature and a readonly property states
// a class value whose static field is a read capability, a view: a class
// value's static fields are under invariant contracts here.
class C {
  static readonly zero: number = 0;
}
export function make(K: { new (): C; readonly zero: number }): C {
  return new K();
}
