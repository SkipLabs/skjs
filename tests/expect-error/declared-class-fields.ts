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

// Two instantiations of a generic ambient class are incompatible when a
// real (annotated) field's type depends on the type argument: here `value: T`
// differs (string vs number). The un-annotated `secret` placeholder is the
// same opaque atom for both instantiations (its identity ignores the type
// arguments — see sharedPlaceholderAtom below), so it is not what drives the
// incompatibility.
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

// Reading an un-annotated ambient field into a concrete type is rejected:
// the placeholder head-expands to an opaque atom, not to `never` (bottom).
// Before #775 it collapsed to `never` — a subtype of everything — so the read
// was unsoundly accepted into any type. tsc treats the field as `any` and
// accepts this read (it reports the missing annotation at the declaration,
// TS7008); SKJS is sound and rejects it.
function readUntypedFieldIntoConcrete(x: AmbientWithUntyped): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
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
