// An object type with construct signatures and other members describes a
// class value with statics, which are bindings of their own here, not members
// of the class value's type.
class C {
  static readonly zero: number = 0;
}
export function make(K: { new (): C; readonly zero: number }): C {
  return new K();
}
