// Two values of a type parameter may both be of any kind, neither known to be
// a primitive nor an object.
export function sameParameter<T>(left: T, right: T): boolean {
  return left === right;
}
