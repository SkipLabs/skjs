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

// Extracting a shape method and free-calling it loses the receiver.
function detachShapeMethod(): number {
  const f = shape.m;
  // @skjs-expect-error A shape method can only be called on the object it was accessed on
  return f();
}

// Laundering a shape method through a no-this function type is rejected: the
// resulting value would permit free calls that lose the receiver.
function launderShapeMethod(): Getter {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return shape.m;
}

// --- Laundering an implicit-class method through no-this types is rejected:
// a no-this function type is a free-call permit, and the method's body reads
// its class off `this` (sound; TS accepts both, SkipLabs/skjs#960). ---

// Passing a class method where a no-this callback is expected detaches it.
declare function callsFree(cb: () => number): number;
function methodAsCallback(): number {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return callsFree(carrier.m);
}

// A property-syntax member promises an extractable free function; a class
// method is not one.
type PropShape = { readonly m: () => number };
function methodIntoPropertySlot(): PropShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return carrier;
}

// --- Attach-only enforcement composes through nested positions. ---

// Through a NESTED object shape: the inner method is still attach-only.
type NestedShape = { outer: { m(): number } };
declare const nested: NestedShape;
function nestedAttachOk(): number {
  return nested.outer.m();
}
function nestedDetach(): number {
  const f = nested.outer.m;
  // @skjs-expect-error A shape method can only be called on the object it was accessed on
  return f();
}
function nestedLaunder(): Getter {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return nested.outer.m;
}

// ...and through a TUPLE element shape.
type TupleShape = [{ m(): number }];
declare const tup: TupleShape;
function tupleAttachOk(): number {
  return tup[0].m();
}
function tupleDetach(): number {
  const f = tup[0].m;
  // @skjs-expect-error A shape method can only be called on the object it was accessed on
  return f();
}

// A property-syntax member carrying a real `this` requirement must NOT inhabit a
// method-syntax shape: the shape erases the requirement, so `o.m()` would run
// with the carrier as `this`, which need not satisfy it (#993).
declare const explicitThisProp: { m: (this: { x: number }) => number };
function propExplicitThisIntoShape(): MethodShape {
  // TODO(#993): should be rejected — the carrier need not satisfy `this: { x }`.
  return explicitThisProp;
}
