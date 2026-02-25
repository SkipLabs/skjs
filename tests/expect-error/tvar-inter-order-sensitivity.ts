/**
 * T & U and U & T orderings should behave identically.
 * Currently, inter(T, U) produces T{cstr: U} — T carries a constraint
 * on U, but not vice versa. Source order T & U vs U & T determines which
 * TVar gets the constraint, leading to order-dependent behavior.
 *
 * Both calls below are unsound: 42 is not <: string (T), so 42 is not
 * in the intersection T & U. Both orderings should reject but don't.
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
  // BUG: accepted but unsound — 42 is not <: string, so not in T & U
  return getU_TU(str, 42);
}

function testUT(): 42 {
  const str: string = "hello";
  // BUG: accepted but unsound — 42 is not <: string, so not in U & T
  return getU_UT(str, 42);
}
