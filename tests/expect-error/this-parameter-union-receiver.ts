// A method shared by every branch of a union receiver is callable: the receiver
// inherently satisfies the method's implicit `this` (the branch it came from).
// The unioned `this` is the intersection of the branches, so the call-site
// receiver check is skipped for an attached call on an implicit `this` — else
// `union <: intersection` would spuriously fail. (tsc --strict accepts all of
// these.)

class A {
  ax: number = 1;
  m(): number {
    return this.ax;
  }
}
class B {
  bx: number = 2;
  m(): number {
    return this.bx;
  }
}
function classUnion(s: A | B): number {
  // FIXME: false positive — a union receiver's shared method should type-check.
  // The union resolves the method's `this` to the intersection of the branches,
  // so the receiver check spuriously fails; corrected later in the series.
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  return s.m();
}

// Primitive unions: each branch's wrapper method declares an explicit `this`
// (string/number), so the unioned `this` is the unsatisfiable intersection
// string & number. FIXME: false positive — distributing the call over the
// receiver branches (a later commit) makes each branch check against its own
// `this`.
function primitiveUnion(x: string | number): string {
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  return x.toString();
}

// Discriminated union, calling a method present on both variants.
interface Circle {
  kind: "circle";
  area(): number;
}
interface Square {
  kind: "square";
  area(): number;
}
function shapeUnion(sh: Circle | Square): number {
  return sh.area();
}
