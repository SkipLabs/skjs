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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return bs;
}
declare function box1Helper(): Box<string>;

// Non-ambient class still requires annotations on public fields.
class RegularPublicNoType {
  // @skjs-expect-error Field 'x' has no initializer and is not assigned in the constructor
  // @skjs-expect-error Member 'x' must have an explicit type annotation
  x;
}

// Reading an un-annotated ambient field into a concrete type should be
// rejected: the field's type is opaque, not a concrete type. It is currently
// accepted because the placeholder collapses to `never` (bottom), a subtype
// of everything (issue #775). tsc treats the field as `any` and accepts this
// read too (it reports the missing annotation at the declaration, TS7008).
function readUntypedFieldIntoConcrete(x: AmbientWithUntyped): void {
  // TODO(#775): should be rejected — the placeholder currently reads as `never`.
  const s: string = x.pub;
}

// Reading the field where its own (opaque) type or a wider `unknown` is
// expected stays accepted: the field is opaque, not unusable.
function readUntypedFieldAsUnknown(x: AmbientWithUntyped): unknown {
  return x.pub;
}

// The write side is rejected: nothing concrete is a subtype of the opaque
// placeholder.
function writeUntypedField(x: AmbientWithUntyped): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x.pub = "hello";
}

// The placeholder ignores the class's type arguments, so two instantiations
// of a generic ambient class whose only differing field is un-annotated are
// mutually assignable — matching tsc, which sees the field as structurally
// identical across instantiations.
declare class OnlySecret<T> {
  secret;
}
declare function onlySecret<T>(): OnlySecret<T>;
function sharedPlaceholderAtom(): OnlySecret<number> {
  return onlySecret<string>();
}
