// The "This would not be an error if this field were readonly" hint should
// appear only when making the field readonly would actually remove the error
// -- i.e. when the getter (covariant) direction already holds and only the
// setter (contravariant) direction fails. Making a field readonly drops the
// setter check; it does nothing for a getter mismatch.

class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

// Legitimate: the getter holds (string <: string | number), only the setter
// fails, so readonly would fix it -- the hint belongs here.
declare function takesWide(b: Box<string | number>): void;
function readonlyWouldHelp(b: Box<string>): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type 'number'
  // @skjs-expect-error-line3 is not assignable to type 'string'
  // @skjs-expect-error-line4 This would not be an error if this field were readonly
  takesWide(b);
}

// Wrong: the getter also fails (an unconstrained U is not a string), so
// readonly would not help -- taking the advice just swaps the setter failure
// for the same getter failure. The hint must not appear here.
declare function takesBoxString(b: Box<string>): void;
function readonlyWouldNotHelp<U>(b: Box<U>): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type 'string'
  // @skjs-expect-error-line3 is not assignable to type 'U'
  // @skjs-expect-error-line4 This would not be an error if this field were readonly
  takesBoxString(b);
}
