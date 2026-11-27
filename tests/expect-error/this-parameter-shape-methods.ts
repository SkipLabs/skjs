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

// A class instance structurally inhabits a method-syntax shape because the
// carrier itself satisfies the method's receiver requirement (#1020).
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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return explicitThisProp;
}

// --- Additional sound carrier cases (restored by #1020) ---

class SubCarrier extends Carrier {
  extra: string = "hi";
}

declare const subCarrier: SubCarrier;
function subclassIntoShape(): MethodShape {
  return subCarrier;
}

class GenericCarrier<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  get(): T {
    return this.v;
  }
}

declare const genCarrier: GenericCarrier<number>;
function genericClassIntoShape(): { get(): number } {
  return genCarrier;
}

interface ICarrier {
  m(): number;
}
declare const iCarrier: ICarrier;
function interfaceIntoShape(): MethodShape {
  return iCarrier;
}

// Union of distinct class instances inhabiting a method-syntax shape.
class AltCarrier {
  k: number = 2;
  m(): number {
    return this.k;
  }
}
declare const unionCarrier: Carrier | AltCarrier;
function unionClassIntoShape(): MethodShape {
  return unionCarrier;
}

// Property-syntax function with explicit `this` when the carrier DOES satisfy it.
function readX(this: { x: number }): number {
  return this.x;
}
declare const withX: { x: number; m: (this: { x: number }) => number };
function explicitThisSatisfiedByCarrier(): MethodShape {
  return withX;
}

// Inline object literal whose properties satisfy the attached function's `this`.
function inlineLiteralSatisfiedThis(): MethodShape {
  return { x: 42, m: readX };
}

// Object literal method syntax (`{ m() { ... } }`) is sound against a shape method.
function objectLiteralMethodIntoShape(): MethodShape {
  const o = {
    x: 42,
    m(): number {
      return this.x;
    },
  };
  return o;
}

// Optional method-syntax shape inhabited by a class instance.
type OptionalMethodShape = { m?(): number };
function classIntoOptionalMethodShape(): OptionalMethodShape {
  return carrier;
}

// Symbol-keyed method-syntax shape inhabited by a class instance.
declare const symM: unique symbol;
class SymCarrier {
  n: number = 1;
  [symM](): number {
    return this.n;
  }
}
declare const symCarrier: SymCarrier;
function symbolMethodIntoShape(): { [symM](): number } {
  return symCarrier;
}

// Overloaded class method inhabiting an overloaded method-syntax shape.
class OverloadedCarrier {
  n: number = 1;
  f(x: number): number;
  f(x: string): string;
  f(x: number | string): number | string {
    return typeof x === "number" ? x + this.n : x;
  }
}
declare const overloadedCarrier: OverloadedCarrier;
function overloadedClassIntoShape(): {
  f(x: number): number;
  f(x: string): string;
} {
  return overloadedCarrier;
}

// Class method with explicit `this: Carrier` still inhabits MethodShape on a Carrier instance.
class ExplicitThisCarrier {
  n: number = 1;
  m(this: ExplicitThisCarrier): number {
    return this.n;
  }
}
declare const explicitThisCarrier: ExplicitThisCarrier;
function explicitThisClassMethodIntoShape(): MethodShape {
  return explicitThisCarrier;
}

// --- Unsound #993 laundering attacks (MUST stay rejected after #1020) ---

// Attack 1: inline object literal `{ m: f }` — must NOT launder `f`'s `this`
// into `ImplicitShape` via field-TVar growth (#1020 obstacle 1).
function inlineLiteralUnsatisfiedThis(): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { m: readX };
}

// Attack 2: inline object literal carrying an extracted class method (`c.m`)
// onto a plain object lacking the nominal class identity.
function inlineLiteralExtractedClassMethod(): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { n: 1, m: carrier.m };
}

// Attack 3: inline object literal with a declared function reference stored in
// a local variable, then placed into an inline literal.
function inlineLiteralLocalVarThis(): MethodShape {
  const fn: (this: { x: number }) => number = readX;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { m: fn };
}

// Attack 4: nested inline object literal laundering `f` in an inner shape.
function nestedInlineLiteralUnsatisfiedThis(): NestedShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { outer: { m: readX } };
}

// Attack 5: extracted class method re-attached via variable binding.
function detachedClassMethodReattached(): MethodShape {
  const f = carrier.m;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { n: 1, m: f };
}

// Attack 6: class method with explicit `this` requiring a subtype (`SubCarrier`)
// must NOT inhabit `MethodShape` when the carrier is only the base `Carrier`.
class NeedsSub {
  n: number = 1;
  m(this: SubNeedsSub): number {
    return this.extra.length;
  }
}
class SubNeedsSub extends NeedsSub {
  extra: string = "ok";
}
declare const baseNeedsSub: NeedsSub;
function baseWithSubclassThisIntoShape(): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return baseNeedsSub;
}

// Attack 7: union where one branch does NOT satisfy `m`'s `this` requirement.
declare const badUnionCarrier:
  | { x: number; m: (this: { x: number }) => number }
  | { m: (this: { x: number }) => number };
function unionOneBranchUnsatisfied(): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return badUnionCarrier;
}

// Attack 8: aliased object literal whose field satisfies `this: { x: 1 }` only
// before mutation — mutating `raw.x = 2` after width-subtyping must be rejected.
function readOne(this: { x: 1 }): number {
  return this.x;
}
function aliasedMutationAfterShapeSubtyping(): MethodShape {
  const raw = { x: 1, m: readOne };
  const o: MethodShape = raw;
  // @skjs-expect-error Type is not assignable to the field's type
  raw.x = 2;
  return o;
}

// Attack 9: symbol-keyed inline literal laundering an unsatisfied `this`.
function symbolInlineLiteralUnsatisfiedThis(): { [symM](): number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { [symM]: readX };
}

// Attack 10: optional property-syntax member with unsatisfied `this` into
// optional method-syntax shape.
declare const optBadProp: { m?: (this: { x: number }) => number };
function optionalBadPropIntoOptionalShape(): OptionalMethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return optBadProp;
}

// Attack 11: mutable property slot carrying an explicit `this` function —
// if `raw` is aliased to a shape and `raw.m` is overwritten with a function
// requiring a different `this` (`readY`), the mutation must be rejected because
// `raw.m` was sealed by the shape check (not widened to `readX | readY`).
function readY(this: { y: string }): number {
  return this.y.length;
}
function aliasedMethodSwapRejected(): MethodShape {
  const raw = { x: 42, m: readX };
  const o: MethodShape = raw;
  // @skjs-expect-error Type is not assignable to the field's type
  raw.m = readY;
  return o;
}

// Attack 12: `{ m: f }` passed directly as a function argument expecting a shape.
declare function takeShape(s: MethodShape): number;
function inlineLiteralArgUnsatisfiedThis(): number {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return takeShape({ m: readX });
}

// Attack 13: `{ m: f }` where `this` is `{ x: number }` and literal has wrong type for `x`.
function inlineLiteralWrongFieldTypeForThis(): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { x: "not a number", m: readX };
}

// Attack 14: extracting a shape method from one carrier and re-attaching it to
// a DIFFERENT object literal (`{ m: other.m }` or `const f = other.m; { m: f }`).
// Because class instances inhabit `MethodShape`, `other.m` may actually be a
// class method reading private/instance fields of `other`; extracting it
// detaches its shape receiver so re-attaching it to a fresh object is rejected.
function detachedShapeMethodReattachedInline(other: MethodShape): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { m: other.m };
}

function detachedShapeMethodReattachedViaVar(other: MethodShape): MethodShape {
  const f = other.m;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { m: f };
}

// Attack 15: spreading a shape carrier onto a new object while overwriting a
// hidden field (`{ ...other, x: "bad" }`) or copying a shape method onto a
// fresh object. Because `other`'s carrier type was erased, copying `other.m`
// onto a fresh object loses the guarantee that `this` matches `other` (and a
// class method may also be omitted by property copy).
function spreadShapeMethodOntoNewObject(other: MethodShape): MethodShape {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...other, x: "bad" };
}

// Attack 16: aliased object literal whose `m` field is overwritten with another
// carrier's shape method (`raw.m = other.m`) after aliasing `raw` to `MethodShape`.
function aliasedMethodSwapWithShapeMethod(other: MethodShape): MethodShape {
  const raw = { x: 42, m: readX };
  const o: MethodShape = raw;
  // @skjs-expect-error Type is not assignable to the field's type
  raw.m = other.m;
  return o;
}
