// A type predicate (`x is T`) is only accepted on a bodyless
// (ambient/interface) signature: SKJS doesn't check the body against the
// claimed predicate, so accepting it on an implemented function/method
// would let the implementation lie about the narrowing.

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isString(x: unknown): x is string {
  return typeof x === "string";
}

class Checker {
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
  isNumber(x: unknown): x is number {
    return typeof x === "number";
  }
}
