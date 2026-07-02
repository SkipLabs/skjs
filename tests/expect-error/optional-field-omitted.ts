// Omitting an optional field is rejected by design: skjs is intentionally
// stricter than tsc here (see tests/expect-error/objects.ts). A source value
// whose type lacks the optional field can still carry an excess property of
// that name with an unrelated type (width subtyping), so viewing it through the
// optional field would read that value at the wrong type. So a sub without the
// optional field (and no covering index) does not satisfy a super that declares
// it. tsc accepts all of these; skjs soundly rejects them.
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
