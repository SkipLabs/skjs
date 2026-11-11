///////////////////////////////////////////////////////////////////////////////
// Class identity: which values have a class instance type.
//
// Interfaces and object types are structural. A class instance type is the
// type of values constructed by that class (or a subclass).
///////////////////////////////////////////////////////////////////////////////

class Pt {
  x: number = 0;
  y: number = 0;
}

class SamePt {
  x: number = 0;
  y: number = 0;
}

class SubPt extends Pt {
  z: number = 0;
}

interface PtShape {
  x: number;
  y: number;
}

// An object literal is not an instance.
function literalToClass(): Pt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line4 Only an instance of class 'Pt' (or a subclass) has this type; use 'new' or an interface for structural shapes
  return { x: 1, y: 2 };
}

// A structurally identical sibling class is a different class.
function siblingToClass(p: SamePt): Pt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

// A value of unknown provenance cannot be laundered into a class type.
function emptyToClass(o: {}): Pt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return o;
}

// A spread copy is a plain object, not an instance.
function spreadCopyToClass(p: Pt): Pt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...p };
}

// A subclass instance is an instance of the base class.
function subclassToBase(p: SubPt): Pt {
  return p;
}

// Class instances still satisfy structural types.
function classToInterface(p: Pt): PtShape {
  return p;
}

function classToObjectType(p: Pt): { x: number } {
  return p;
}

function constructed(): Pt {
  return new Pt();
}

// keyof and spread see only the declared members.
function keyofMembers(p: Pt): number {
  const k: keyof Pt = "x";
  __SKJS_show(k, '"x" | "y"');
  return p[k];
}

function spreadMembers(p: Pt): { x: number; y: number } {
  return { ...p };
}

// instanceof proves identity: the narrowed value has the class type, whether
// the scrutinee already matched the class's members or not.
function instanceofIdentity(o: PtShape): Pt {
  if (o instanceof Pt) {
    return o;
  }
  return new Pt();
}

function instanceofIdentityPartial(o: { x: number }): Pt {
  if (o instanceof Pt) {
    return o;
  }
  return new Pt();
}

// Type arguments stay structural.
class Holder<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function sameHolder(h: Holder<number>): Holder<number> {
  return h;
}

function readonlyWidenedHolder(h: Holder<number>): {
  readonly v: number | string;
} {
  return h;
}

// Two unrelated classes have no common instance.
class Other {
  x: number = 0;
  y: number = 0;
}

function intoUnrelatedIntersection(p: Pt): Pt & Other {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

// `implements` is a structural contract: the implementer is checked against
// the class's members, but it is not an instance of that class.
class ImplPt implements Pt {
  x: number = 1;
  y: number = 2;
}

function implementerToClass(p: ImplPt): Pt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

function implementerToShape(p: ImplPt): PtShape {
  return p;
}

// An interface extending a class inherits its members, not its identity.
interface PtLike extends Pt {
  label: string;
}

function literalToClassInterface(): PtLike {
  return { x: 1, y: 2, label: "a" };
}

// A subclass instance meets its base in an intersection.
function subclassIntersection(s: SubPt): Pt & SubPt {
  return s;
}

// The diagnostic names the class the target requires, not one of its bases.
function literalToSubclass(): SubPt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line4 Only an instance of class 'Pt' (or a subclass) has this type; use 'new' or an interface for structural shapes
  return { x: 1, y: 2, z: 3 };
}

function baseToSubclass(p: Pt): SubPt {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}
