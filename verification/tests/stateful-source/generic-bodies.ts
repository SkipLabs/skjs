/**
 * Generic bodies that copy T: a const alias, and the first of two parameters.
 * These are not `return x` of a single parameter.
 */
function bind<T>(x: T): T {
  const y: T = x;
  return y;
}

function fst<T>(x: T, y: T): T {
  return x;
}
