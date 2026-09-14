type ElementOf<T extends readonly unknown[]> = T[number];

// The abstract body check must not erase the dependency that an explicit
// instantiation later uses to specialize the result.
// @skjs-expect-error Indexed access on an abstract type is not yet supported by SKJS; use a known object or array shape with explicit type parameters
function fabricatedElement<T extends readonly unknown[]>(xs: T): ElementOf<T> {
  return "wrong";
}
function numericElement(xs: number[]): number {
  return fabricatedElement<number[]>(xs);
}

// Even a real indexed read needs an abstract indexed-type representation
// when the whole array type is the parameter.
function abstractRead<T extends readonly unknown[]>(
  xs: T,
  // @skjs-expect-error Indexed access on an abstract type is not yet supported by SKJS; use a known object or array shape with explicit type parameters
): T[number] | undefined {
  return xs[0];
}

// A known array shape can retain its symbolic element parameter directly.
function elementRead<E>(xs: readonly E[]): ElementOf<readonly E[]> | undefined {
  return xs[0];
}
function concreteElement(xs: readonly number[]): ElementOf<readonly number[]> {
  return xs[0] ?? 0;
}

type Keys<T> = keyof T;
// @skjs-expect-error keyof on an abstract type is not yet supported by SKJS; use a known object or array shape with explicit type parameters
function fabricatedKey<T>(x: T): Keys<T> {
  return "wrong";
}
function concreteKey(x: { good: number }): "good" {
  return fabricatedKey<{ good: number }>(x);
}
function shapeKey<E>(x: { good: E }): Keys<{ good: E }> {
  return "good";
}

// A string upper bound is not the complete string domain. A real string
// union member, in contrast, absorbs the dependent interpolation.
type TextOf<T extends string> = `${T}`;
function fabricatedText<T extends string>(x: T): TextOf<T> {
  return "wrong";
}
function concreteText(): "good" {
  return fabricatedText<"good">("good");
}
type AbsorbedText<T extends string> = `${T | string}`;
function absorbedText<T extends string>(x: T): AbsorbedText<T> {
  return "any string";
}
