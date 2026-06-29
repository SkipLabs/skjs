// An omitted optional field is allowed: a source whose type lacks an optional
// field of the target may still satisfy it — `f?:` permits exactly that
// absence. tsc accepts all of these forms.
interface Foo {
  readonly a: number;
  b?: string;
}

// @skjs-expect-error This class incorrectly implements 'Foo'
class ImplementsOmitting implements Foo {
  readonly a: number = 1;
}

function viaStructuralValue(x: { readonly a: number }): Foo {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function viaInstance(): Foo {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new ImplementsOmitting();
}
