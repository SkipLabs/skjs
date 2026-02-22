type arrayNumberOrArrayString = Array<number> | Array<string>;

// Involves an inst which is both an intersection and a named type
// while destructing the array type
function interWithTop<T>(...x: T[] & arrayNumberOrArrayString): T {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  return result;
}

function checkIntersectionWithTopIsNotBottom(): number {
  return interWithTop<number>(0) + 1; // ensure the result is a (subtype of a) number
}

// Same shape as above, only binder name differs (S instead of T).
function interWithTopS<S>(...x: S[] & arrayNumberOrArrayString): S {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  return result;
}

function checkIntersectionWithTopSIsNotBottom(): number {
  // Name-sensitive behavior probe: this call differs from the T-binder version.
  return interWithTopS<number>(0) + 1;
}
