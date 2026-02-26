/**
 * T & U and U & T orderings should behave identically.
 * With TInter, the intersection is symmetric: both orderings are equivalent.
 */

function getU_TU<T, U>(t: T, both: T & U): U {
  return both;
}
function getU_UT<T, U>(t: T, both: U & T): U {
  return both;
}

// T=string, both=42. The value 42 is not <: string (T),
// so 42 is not in the intersection T & U. Both orderings should reject.
function testTU(): 42 {
  const str: string = "hello";
  // @skjs-expect-error Invalid call
  return getU_TU(str, 42);
}

function testUT(): 42 {
  const str: string = "hello";
  // @skjs-expect-error Invalid call
  return getU_UT(str, 42);
}
