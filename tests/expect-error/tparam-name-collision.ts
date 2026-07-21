// Two distinct type parameters can reach one diagnostic under the same name.
// The qualified id that tells them apart is deliberately not user-visible (see
// TypePp::tparamName), so the message reads as a tautology: "Type 'T' is not
// assignable to type 'T'". These cases pin that text; issue #919 tracks making
// it readable.
//
// The collision arises two ways: a hidden type argument minted by `instanceof`
// narrowing (a different one per check, so two checks never share), and
// ordinary source shadowing of a type parameter's name.

class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

class Tagged<T extends string> {
  tag: T;
  constructor(tag: T) {
    this.tag = tag;
  }
}

// Two `instanceof` checks mint two hidden arguments; both print as 'T'.
function crossExchange(x: unknown, y: unknown): void {
  if (x instanceof Box && y instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Box#T#2'
    // @skjs-expect-error-line3 is not assignable to type 'Box#T#1'
    // @skjs-expect-error-line4 Two different types with this name exist, but they are unrelated; the '#' suffixes are display-only and cannot be written in source
    x.v = y.v;
  }
}

// A declared bound is printed with the name, so the collision survives it.
function crossTagged(x: unknown, y: unknown): void {
  if (x instanceof Tagged && y instanceof Tagged) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Tagged#T#2 extends string'
    // @skjs-expect-error-line3 is not assignable to type 'Tagged#T#1 extends string'
    // @skjs-expect-error-line4 Two different types with this name exist, but they are unrelated; the '#' suffixes are display-only and cannot be written in source
    x.tag = y.tag;
  }
}

// The same collision through a call, where the message is built by a different
// site: note the contravariance line, which names both parameters too. The
// type arguments an example would list are the two hidden arguments, which
// have no name in source, so the advice is given without the `e.g., <...>`
// example rather than suggesting something unwritable.
declare function sharedLen<T>(a: Array<T>, b: Array<T>): number;
function sharedArrays(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type 'Array#T#2'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T#1'
    // @skjs-expect-error-line4 Consider adding explicit type arguments
    // @skjs-expect-error-line5 Function parameter types are checked contravariantly: target parameter type 'Array#T#2' must be assignable to source parameter type 'Array#T#1'
    // @skjs-expect-error-line6 Two different types with this name exist, but they are unrelated; the '#' suffixes are display-only and cannot be written in source
    return sharedLen(u, w);
  }
  return 0;
}

// A parameter keeps its number across every message that disambiguates it.
// These two assign in opposite directions between the same pair, so the
// numbers have to swap between the messages -- numbering by where a name
// landed in the sentence would print both errors identically.
function swapDirectionA(x: unknown, y: unknown): void {
  if (x instanceof Box && y instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Box#T#2'
    // @skjs-expect-error-line3 is not assignable to type 'Box#T#1'
    x.v = y.v;
  }
}

function swapDirectionB(x: unknown, y: unknown): void {
  if (x instanceof Box && y instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Box#T#1'
    // @skjs-expect-error-line3 is not assignable to type 'Box#T#2'
    y.v = x.v;
  }
}

// Plain source shadowing, no `instanceof` involved: the method's own `T` hides
// the class's. This is the case tsc reports as TS2719.
class Shadow<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  set<T>(x: T): void {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'T#2'
    // @skjs-expect-error-line3 is not assignable to type 'T#1'
    // @skjs-expect-error-line4 Two different types with this name exist, but they are unrelated; the '#' suffixes are display-only and cannot be written in source
    this.v = x;
  }
}
