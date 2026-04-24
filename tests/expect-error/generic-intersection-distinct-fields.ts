// An intersection A<U> & B<V> of two distinct generic interfaces exposes
// fields from both sides, and accepts a concrete record that conforms to
// their union of fields.
interface A<T> {
  f: T;
  g: number;
}
interface B<T> {
  f: T;
  h: string;
}

function foo<U, V>(x: A<U> & B<V>): boolean {
  return x.g > 0 && x.h.length > 0;
}

function main(): boolean {
  return foo({ f: true, g: 0, h: "yo" });
}
