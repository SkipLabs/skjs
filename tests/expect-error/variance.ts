type arrayBooleanOrArrayString = Array<boolean> | Array<string>;

// The intersection does not behave as expected since it appears in
// contravariant position
function interWithTop<T>(...x: T[] & arrayBooleanOrArrayString): T {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  // TODO: Intersection on index field is not precise enough
  // @skjs-expect-error Invalid return type
  return result;
}

// We should not be able to call interWithTop with T instantiated to number
function checkIntersectionWithTopIsNotBottom(): number {
  return interWithTop<number>(0) + 1;
}
