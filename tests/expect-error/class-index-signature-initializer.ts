// Pins current behavior: a class index signature `[a: string]: T` is
// incorrectly treated as a field named 'a' by the no-constructor
// definite-assignment check, producing a spurious "has no initializer"
// error. The next commit fixes this, turning the first annotation below
// into a positive case.
class C {
  // @skjs-expect-error Field 'a' has no initializer and is not assigned in the constructor
  [a: string]: number;
  // @skjs-expect-error Field 'v' has no initializer and is not assigned in the constructor
  v: number;
}
