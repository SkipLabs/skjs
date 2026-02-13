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
  // @skjs-expect-error Invalid call. Unexpected type for ...
  return interWithTop<number>(0) + 1;
}

// Same shape as above, only binder name differs (S instead of T).
function interWithTopS<S>(...x: S[] & arrayBooleanOrArrayString): S {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  // TODO: Intersection on index field is not precise enough
  // @skjs-expect-error Invalid return type
  return result;
}

function checkIntersectionWithTopSIsNotBottom(): number {
  // Name-sensitive behavior probe: this call differs from the T-binder version.
  // @skjs-expect-error Invalid call. Unexpected type for ...
  return interWithTopS<number>(0) + 1;
}
