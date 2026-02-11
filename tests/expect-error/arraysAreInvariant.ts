type arrayNumberOrArrayString = Array<number> | Array<string>;

// Involves an inst which is both an intersection and a named type
// while destructing the array type
function interWithTop<T>(...x: T[] & arrayNumberOrArrayString): T {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  return result;
}

function checkIntersectionWithTopIsNotBottom(): number {
  // @skjs-expect-error Invalid call. Unexpected type for ...
  return interWithTop<number>(0) + 1;
}

// Same shape as above, only binder name differs (S instead of T).
function interWithTopS<S>(...x: S[] & arrayNumberOrArrayString): S {
  const result = x[0];
  if (result === undefined) throw "Array is empty";
  return result;
}

function checkIntersectionWithTopSIsNotBottom(): number {
  // Name-sensitive behavior probe: this call differs from the T-binder version.
  // @skjs-expect-error Invalid call. Unexpected type for ...
  return interWithTopS<number>(0) + 1;
}

// ReadonlyArray is covariant: readonly Dog[] is a subtype of readonly Animal[]
interface Animal {
  name: string;
}
interface Dog extends Animal {
  breed: string;
}

function readonlyArrayIsCovariant(dogs: readonly Dog[]): readonly Animal[] {
  return dogs;
}

// The reverse does not hold
function readonlyArrayIsNotContravariant(
  animals: readonly Animal[],
): readonly Dog[] {
  // @skjs-expect-error Invalid return type
  return animals;
}

// Array<T> is a subtype of readonly T[]
function arrayIsSubtypeOfReadonlyArray(dogs: Dog[]): readonly Dog[] {
  return dogs;
}

// readonly T[] is not a subtype of Array<T>
function readonlyArrayIsNotSubtypeOfArray(dogs: readonly Dog[]): Dog[] {
  // @skjs-expect-error Invalid return type
  return dogs;
}

// Known limitation: indexOf, includes, lastIndexOf, concat are commented out
// on ReadonlyArray because T in contravariant position prevents covariant subtyping.
function readonlyArrayMissingMethods(xs: readonly number[]): void {
  // @skjs-expect-error Invalid call
  // @skjs-expect-error Invalid index key
  xs.indexOf(1);
}
