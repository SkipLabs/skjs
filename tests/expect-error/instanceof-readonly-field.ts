// `instanceof` narrowing must not grant write access a value's declared type
// withheld. A field the scrutinee declared `readonly` should stay readonly
// through the narrowing: narrowing may restrict what can be written, never
// widen it. Issue #898.

class Cell<T> {
  a: T;
  b: T;
  constructor(a: T, b: T) {
    this.a = a;
    this.b = b;
  }
}

// The scrutinee's fields are readonly and of different types, so it is not a
// `Cell<t>` for any single `t`; narrowing intersects it with `Cell<skolem>`.
// That intersection keeps the fields readonly, so writing one field into the
// other -- which would corrupt a value the caller declared it could not mutate
// -- is rejected.
function readonlyStaysReadonly(o: {
  readonly a: string;
  readonly b: number;
}): void {
  const x: { readonly a: string; readonly b: number } = o;
  if (x instanceof Cell) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'number & Cell#T'
    // @skjs-expect-error-line3 is not assignable to type 'never'
    x.a = x.b;
  }
}

// A mutable-field scrutinee (here `unknown`, whose fields come entirely from
// the class view) is unaffected: the write is rejected through the rigid
// hidden type argument, not readonly.
function mutableRejectedByRigidity(x: unknown): void {
  if (x instanceof Cell) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'Cell#T'
    x.a = "s";
  }
}
