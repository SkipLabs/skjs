/**
 * When a parameter has type T & U, both T and U should be narrowed to
 * the intersection of their inferred types.
 */

function getU<T, U>(t: T, u: U, both: T & U): U {
  return both;
}

function getT<T, U>(t: T, u: U, both: T & U): T {
  return both;
}

function testT(): 42 {
  const num: number = 42;
  return getT(42, num, 42);
}

// Check U is number (not 42) by assigning to number
function testUIsNumber(): number {
  const num: number = 42;
  return getU(42, num, 42);
}

// U should be 42 (narrowed via intersection with T)
function testU(): 42 {
  const num: number = 42;
  return getU(42, num, 42);
}
