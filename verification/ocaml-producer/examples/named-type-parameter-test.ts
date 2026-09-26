// A `typeof` test on a value of a type parameter narrows it to `T & number`,
// which no clause states.
export function onlyNumber<T extends number | string>(x: T): number {
  if (typeof x === "number") {
    return x;
  }
  return 0;
}
