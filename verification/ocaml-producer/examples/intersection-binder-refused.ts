// An intersection with a type parameter is known only at an instance.
interface A {
  a: number;
}
export function pick<T>(x: T & A): T {
  return x;
}
