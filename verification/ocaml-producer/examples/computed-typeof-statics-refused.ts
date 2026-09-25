// A class value's statics are bindings of their own: `typeof C` of a class
// with one has no type here.
class C {
  static readonly zero: number = 0;
}
export function make(K: typeof C): C {
  return new K();
}
