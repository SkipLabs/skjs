// Type parameter inference from class constructor arguments.

class Holder<T> {
  constructor(public value: T) {}
}

// When Holder is instantiated with "hello", T is inferred as "hello".
// When T is "hello", holder.value has type "hello" and is not assignable to number.
function getNumber(): number {
  const holder = new Holder("hello");
  // @ts-expect-error Invalid return type
  return holder.value;
}
