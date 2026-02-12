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

  // Box<"foo"> satisfies T extends Box<string> ("foo" extends string),
  // so this matches the T branch of the union.
  const badBox: Box<"foo"> = new Box("foo");
  takeBoxOrNumber(badBox);

  // Same behavior regardless of binder name (S vs T).
  takeBoxOrNumberS(badBox);
}
