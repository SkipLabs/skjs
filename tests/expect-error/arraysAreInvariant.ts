type arrayNumberOrArrayString = Array<number> | Array<string>;

// Involves an inst which is both an intersection and a named type
// while destructing the array type
function interWithTop<T>(...x: T[] & arrayNumberOrArrayString): T {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  // Intersection on index field is now precise enough to type this return.
  return result;
}

function checkIntersectionWithTopIsNotBottom(): number {
  return interWithTop<number>(0) + 1; // ensure the result is a (subtype of a) number
}
