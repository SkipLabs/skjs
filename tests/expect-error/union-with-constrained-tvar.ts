// Test: Union parameter types with constrained type variables.
//
// When a function has parameter type `T | U` where `T` has a constraint,
// an argument is valid if it matches ANY branch of the union.

class Box<T> {
  value: T;
  constructor(v: T) {
    this.value = v;
  }
}

// Parameter type is `T | number` where T has constraint `Box<string>`.
function takeBoxOrNumber<T extends Box<string>>(x: T | number): void {}
// Same shape as above, only binder name differs (S instead of T).
function takeBoxOrNumberS<S extends Box<string>>(x: S | number): void {}

function test(): void {
  // A number matches the `number` branch of the union.
  takeBoxOrNumber(42);

  // A Box<"foo"> does not satisfy T extends Box<string> (literal vs string),
  // and is not assignable to number, so this should fail.
  const badBox: Box<"foo"> = new Box("foo");
  // @skjs-expect-error Invalid call
  takeBoxOrNumber(badBox);

  // Name-sensitive behavior probe: this variant can differ from the T-binder one.
  // @skjs-expect-error Invalid call
  takeBoxOrNumberS(badBox);
}
