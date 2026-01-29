/**
 * UNSOUND: Class constructor type parameter inference defaults to top.
 *
 * When a generic class constructor is called without explicit type arguments,
 * the type parameter is not inferred from constructor arguments - it defaults
 * to top, allowing any type to be read from fields.
 *
 * This test passes type checking but crashes at runtime.
 */

class Holder<T> {
  constructor(public value: T) {}
}

// new Holder("hello") should infer Holder<"hello">, but T defaults to top.
// holder.value is typed as top, so returning it as number is accepted.
// At runtime, holder.value is "hello", not a number.
function getNumber(): number {
  const holder = new Holder("hello");
  // @ts-expect-error Type 'string' is not assignable to type 'number'.
   return holder.value;
}

// Crashes: "hello".toFixed(2) is not a function
function crash(): string {
  return getNumber().toFixed(2);
}
