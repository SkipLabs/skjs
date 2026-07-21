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

// The same holds for a readonly index. A `ReadonlyArray` narrowed by
// `instanceof Array` is intersected with the mutable `Array` view; the readonly
// number index must stay readonly, so writing one element into another -- which
// a rigid element type alone accepts (both sides are the same hidden type) --
// is rejected. UNSOUND: accepted today; the fix rejects it. tsc narrows to a
// mutable `string[]` and accepts it too.
function readonlyIndexStaysReadonly(a: ReadonlyArray<string>): void {
  if (a instanceof Array) {
    const e = a[1];
    if (e !== undefined) {
      a[0] = e;
    }
  }
}
