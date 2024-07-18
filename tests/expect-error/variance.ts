// This currently normalizes to Top
type arrayBooleanOrArrayString = Array<boolean> | Array<string>;

// The intersection does not behave as expected since it appears in
// contravariant position
function interWithTop<T>(...x: T[] & arrayBooleanOrArrayString): T {
    return x[0];
}

// We should not be able to call interWithTop with T instantiated to number
function checkIntersectionWithTopIsNotBottom(): number {
  return interWithTop(0) + 1;
}
