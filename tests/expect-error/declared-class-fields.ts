// Ambient (declare-wrapped) classes have no method bodies for SKJS to
// type-check (TypeChecker#class_ skips them at the def level), so they
// may omit type annotations on their fields. Whatever uses such a
// field as a real type still errors at use site, because the
// placeholder type synthesized by addFields is opaque.

declare class AmbientWithUntyped {
  private a;
  pub;
}

// addFields walks the parent's TFields here, exercising the synthesis.
class _UseAmbient extends AmbientWithUntyped {}

// Identity passes — same class, same placeholder per field.
function passThrough(x: AmbientWithUntyped): AmbientWithUntyped {
  return x;
}

// Two instantiations of a generic ambient class are incompatible
// because the placeholder's targs differ.
declare class Box<T> {
  secret;
  value: T;
}

function box1(): Box<number> {
  let bs: Box<string> = box1Helper();
  // @skjs-expect-error Invalid return type
  return bs;
}
declare function box1Helper(): Box<string>;

// Non-ambient class still requires annotations on public fields.
class RegularPublicNoType {
  // @skjs-expect-error Type annotation expected for 'x'
  // @skjs-expect-error Uninitialized field 'x'
  x;
}
