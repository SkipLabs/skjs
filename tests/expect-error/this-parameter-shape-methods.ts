// Method-syntax members of object-literal types (`{ m(): R }`) versus
// property-syntax members (`{ m: () => R }`).
//
// Target rules (sound; stricter than TS where noted):
//   - A method-syntax member is ATTACH-ONLY: its receiver is the object it is
//     accessed on, so attached calls are sound for any inhabitant; extracting
//     it and calling it free, or laundering it through a no-this function
//     type, is rejected (TS accepts both, unsoundly — SkipLabs/skjs#960).
//   - A property-syntax member is a genuinely free function: only receiver-
//     independent functions inhabit it.
//   - Class instances (and, once stubs declare `this`, primitives) inhabit
//     method-syntax shapes; that is what keeps structural typing working.
//
// Staged: shape members currently behave like plain no-this functions; the
// annotations flip as the attach-only machinery lands.

class Carrier {
  n: number = 1;
  m(): number {
    return this.n;
  }
}

type MethodShape = { m(): number };
type Getter = () => number;

declare const shape: MethodShape;
declare const carrier: Carrier;

// Attached calls through a method-syntax shape are always fine.
function attachOk(): number {
  return shape.m();
}

// A class instance inhabits a method-syntax shape.
function widthOk(): MethodShape {
  return carrier;
}

// FIXME: accepted for now — extracting a shape method and free-calling it
// loses the receiver; rejected once shape members are attach-only.
function detachShapeMethod(): number {
  const f = shape.m;
  return f();
}

// Laundering a shape method through a no-this function type is rejected: the
// resulting value would permit free calls that lose the receiver.
function launderShapeMethod(): Getter {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return shape.m;
}
